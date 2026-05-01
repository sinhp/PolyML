/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monad.Monadicity
import PolyML.Monoidal.NNO

/-!
# Free Monoid Monad

In this file, we prove that in a list-arithmetic category, the list object `list A` is a free monoid on the object `A`.

This provides a left adjoint to the forgetful functor from `Mon C` to `C`.

The development here is a categorification of `Mathlib.Algebra.FreeMonoid.Basic` for types.
-/


namespace CategoryTheory

open Category CategoryTheory ListArithmetic MonoidalCategory MonObj NNO Limits

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [ListArithmetic C]


/-- The free monoid functor given by the list objects of a list-arithmetic category. -/
@[simps]
def freeMon : C ⥤ Mon C where
  obj A := Mon.mk (list A)
  map {X Y} f := Mon.Hom.mk' (list.map f) (list.map_nil) (list.append_map)
  map_id := by aesop
  map_comp := by aesop

/-- Extends the isomorphism `listUnitIsoNNO` of the types to the monoids. -/
def freeMonUnitIsoMonNNO [BraidedCategory C] :
    (freeMon C).obj (𝟙_ C) ≅ Mon.mk N := by
  refine Mon.mkIso (listUnitIsoNNO C) ?_ ?_
  · simp [listUnitIsoNNO]
    aesop
  · simp [listUnitIsoNNO]
    dsimp [MonObj.mul, add, iter, prc]
    apply list.prc_uniq
    · simp only [list.whiskerRight_nil_append, comp_id]
    · nth_rw 1 [list.append]
      rw [← Category.assoc, list.cons_prc]
      simp only [id_whiskerLeft, Category.assoc, Iso.hom_inv_id_assoc, Iso.cancel_iso_hom_left]
      dsimp [list.append]

namespace list

variable {C}

/-- Given a monoid object `M` in `C`, we define a morphism from `list X` to `M.X` by folding the list with the multiplication of the monoid. -/
def lift {X : C} {M : Mon C} (f : X ⟶ M.X) : list X ⟶ M.X :=
  list.foldr ((f ▷ M.X) ≫ μ[M.X]) η[M.X]

theorem lift_one {X : C} {M : Mon C} {f : X ⟶ M.X} :
    η ≫ list.lift f = η := by
  dsimp [lift, list.foldr, MonObj.one, list.nil]
  rw [plist.nil_rc]

theorem lift_one_whiskerRight {M : Mon C} {f : X ⟶ M.X} {_ : C} :
  (η ▷ X) ≫ (list.lift f ▷ X) = η ▷ X := by
  dsimp [lift, list.foldr, MonObj.one, list.nil]
  apply plist.whiskerRight_nil_whiskerRight_rc


theorem lift_mul {X : C} {M : Mon C} {f : X ⟶ M.X} :
    μ ≫ list.lift f = (list.lift f ⊗ₘ list.lift f) ≫ μ := by

  -- 1. Prove the LHS equals the explicit primitive recursion
  have h_LHS : μ ≫ list.lift f = prc (list.lift f) ((f ▷ M.X) ≫ μ) := by
    -- Force Lean to see the source monoid multiplication as list.append
    dsimp [MonObj.mul]

    apply list.prc_uniq
    · -- Base case: nil ▷ list X ≫ (append ≫ lift f) = (λ_ (list X)).hom ≫ lift f
      rw [← Category.assoc]
      -- Evaluate the base case of append
      rw [list.whiskerRight_nil_append]

    · -- Step case: cons ▷ list X ≫ (append ≫ lift f) = ...
      rw [← Category.assoc]

      -- 1. Unroll the step case for list.append
      dsimp [list.append]
      rw [list.cons_prc]

      -- 2. Associate to isolate the (cons ≫ plist.rc ...) part
      simp only [Category.assoc]

      -- 3. THE FIX: Unfold list.cons to plist.cons so the pattern matches!
      dsimp [list.lift, list.foldr, list.cons]

      -- 4. Unroll the step case for plist.rc.
      -- We use 'simp only' because it handles categorical associativity natively.
      simp only [plist.cons_rc]
      aesop

  -- 2. Prove the RHS equals the exact same primitive recursion
  have h_RHS : (list.lift f ⊗ₘ list.lift f) ≫ μ = prc (list.lift f) ((f ▷ M.X) ≫ μ) := by
    apply list.prc_uniq

    · -- ==========================================
      -- BASE CASE
      -- ==========================================
      rw [MonoidalCategory.tensorHom_def]
      simp only [Category.assoc]

      -- 1. FIX ASSOCIATIVITY: Group the first two whiskers together
      rw [← Category.assoc (list.nil ▷ list X) (list.lift f ▷ list X)]

      -- 2. Merge nil into the left 'lift f'
      rw [← MonoidalCategory.comp_whiskerRight]

      -- 3. THE FIX: Bridge the syntactic gap between 'nil' and 'η'.
      -- By explicitly declaring the type, we force Lean to unify them.
      have h_nil_lift : list.nil ≫ list.lift f = η := list.lift_one
      rw [h_nil_lift]

      -- 4. SWAP: Group the Right Whisker (η) and Left Whisker (lift f) and swap them!
      rw [← Category.assoc (η ▷ list X) (M.X ◁ list.lift f)]
      rw [← MonoidalCategory.whisker_exchange]
      simp only [Category.assoc]

      -- 5. Reduce using the Monoid left unit law
      -- Lean already groups the final two terms as ((η ▷ M.X) ≫ μ).
      -- This matches MonObj.one_mul perfectly!
      rw [MonObj.one_mul]

      -- 6. We now have (𝟙_ C ◁ lift f) ≫ (λ_ M.X).hom.
      -- Reverse the naturality of the left unitor to turn it into the RHS!
      rw [← MonoidalCategory.leftUnitor_naturality]

    ·  -- ==========================================
      -- STEP CASE
      -- ==========================================
      rw [MonoidalCategory.tensorHom_def]
      simp only [Category.assoc]

      -- 1. THE FIX: Group using `list.cons` because it hasn't been unfolded yet!
      rw [← Category.assoc (list.cons ▷ list X) (list.lift f ▷ list X)]
      rw [← MonoidalCategory.comp_whiskerRight]

      -- 2. NOW we unfold lift and cons to expose the primitive 'plist' recursor
      dsimp [list.lift, list.foldr, list.cons]

      -- 3. Evaluate the recursion inside the newly merged whisker
      rw [plist.cons_rc]

      -- 4. Distribute the right-whisker (▷ list X) across the new composition.
      rw [MonoidalCategory.comp_whiskerRight]
      rw [MonoidalCategory.comp_whiskerRight]
      simp only [Category.assoc]

      -- 5. Swap 1 (LHS): Move M.X ◁ lift f past μ ▷ list X.
      rw [← Category.assoc (μ ▷ list X) (M.X ◁ plist.rc η (f ▷ M.X ≫ μ))]
      rw [← MonoidalCategory.whisker_exchange]
      simp only [Category.assoc]

      -- 6. Expand the RHS and FLATTEN the brackets!
      -- Adding Category.assoc here destroys the ( ... ≫ X ◁ μ ) block.
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

      -- 7. Swap 2 (RHS): Forward whisker_exchange
      -- Now X ◁ μ and f ▷ M.X are perfectly adjacent and can be swapped.
      rw [← Category.assoc (X ◁ μ) (f ▷ M.X)]
      rw [MonoidalCategory.whisker_exchange]
      simp only [Category.assoc]

      -- 8. Apply Monoid Associativity!
      rw [MonObj.mul_assoc]

      -- 9. THE FINAL SWAP (LHS): Swap `f` and `rc`.
      -- We group the Right Whisker (f) and Left Whisker (rc), then reverse-exchange them.
      rw [← Category.assoc (f ▷ M.X ▷ list X) ((M.X ⊗ M.X) ◁ plist.rc η (f ▷ M.X ≫ μ))]
      rw [← MonoidalCategory.whisker_exchange]

      -- 10. The core morphism order is now PERFECTLY IDENTICAL on both sides!
      -- Let the simplifier crush the remaining structural α_ homs.
      simp
      aesop


  -- 3. Conclude the theorem!
  rw [h_LHS, h_RHS]


/-- The underlying functor of the list monad. -/
def functor : C ⥤ C := freeMon C ⋙ Mon.forget C

theorem functor_obj (A : C) : functor.obj A = list A := by
  rfl

theorem functor_map {A B : C} (f : A ⟶ B) : functor.map f = list.map f := by
  rfl

/-- The adjoint transposition equivalence of the hom-sets. -/
def homEquiv (X : C) (M : Mon C) : ((freeMon C).obj X ⟶ M) ≃ (X ⟶ (Mon.forget C).obj M) where
  toFun f := list.singleton ≫ f.hom
  invFun f := Mon.Hom.mk' (list.lift f) list.lift_one list.lift_mul
  left_inv f := by
    -- 1. Use `ext` to prove equality on the underlying morphisms in C.
    ext

    -- 2. Explicitly state the evaluated form we want to prove.
    change list.lift (list.singleton ≫ f.hom) = f.hom

    -- 3. Flip it so the recursor is on the right
    symm

    -- 4. Unfold list.lift and list.foldr to expose the primitive plist.rc
    dsimp [list.lift, list.foldr]

    -- 5. Apply the uniqueness principle
    apply plist.rc_uniq

    · -- ==========================================
      -- BASE CASE
      -- ==========================================
      -- Since `list.nil` is definitionally the unit (`η`) of the free monoid,
      -- we just apply the generic unit-preservation axiom for `f.hom`.
      exact IsMonHom.one_hom f.hom

    · -- ==========================================
      -- STEP CASE
      -- ==========================================

      -- 1. THE DEFINITIONAL SLEDGEHAMMER:
      -- Force Lean to display `plist.cons` as `list.cons` so the rewrite can see it!
      change list.cons ≫ f.hom = _

      -- 2. RELATE CONS TO APPEND:
      rw [← list.singleton_append_eq_cons]

      -- 3. Group the append with f.hom
      rw [Category.assoc]

      -- 4. APPLY THE HOMOMORPHISM AXIOM:
      -- We use `erw` (evaluate rewrite) so Lean looks through the `append`
      -- abbreviation and recognizes it as the monoidal `μ`!
      erw [IsMonHom.mul_hom f.hom]

      -- 5. Expand the tensor product of f.hom
      -- This gives us `(list X ◁ f.hom) ≫ (f.hom ▷ M.X)`
      rw [MonoidalCategory.tensorHom_def']
      simp only [Category.assoc]

      -- 6. THE MAGIC TENSOR SWAP!
      -- Group the first two whiskers together using a blank `assoc`
      -- 6. THE MAGIC TENSOR SWAP!
      -- Group the first two whiskers together using a blank `assoc`
      rw [← Category.assoc]

      -- UNIFY THE SYNTAX: Force Lean to display the free monoid object as `list X`
      change (list.singleton ▷ list X ≫ list X ◁ f.hom) ≫ _ = _

      -- Collapse them into `singleton ⊗ₘ f.hom`...
      rw [← MonoidalCategory.tensorHom_def]

      -- ... and re-expand them using the PRIMED definition to cross their wires!
      -- This magically transforms them into `(X ◁ f.hom) ≫ (singleton ▷ M.X)`
      rw [MonoidalCategory.tensorHom_def']
      simp only [Category.assoc]
      simp

      -- At this point, the goal is perfectly reduced to:
      -- list.cons ≫ f.hom = (list.singleton ▷ list X) ≫ μ[(freeMon C).obj X.X] ≫ f.hom
  right_inv f := by
    -- 1. Explicitly state the evaluated form of `toFun (invFun f) = f`
    change list.singleton ≫ list.lift f = f

    -- 2. Unfold the list operations
    dsimp [list.singleton, list.lift, list.foldr]
    rw [Category.assoc, Category.assoc]

    -- 3. Unfold cons to its primitive form to avoid pattern-matching errors
    dsimp [list.cons]

    -- 4. Evaluate the recursive step and the nil base case
    -- (Use plist.rc_cons or plist.cons_rc depending on your exact lemma name!)
    rw [plist.cons_rc, list.nil]

    -- 5. Apply the exact same structural crush from your aggregator_singleton proof!
    simp only [plist.whiskerLeft_nil_whiskerLeft_rc_assoc]


    -- We are starting from the goal: (ρ_ X).inv ≫ X ◁ η ≫ f ▷ M.X ≫ μ = f

    -- 1. Group the two whiskers together so the pattern matcher can see them.
    rw [← Category.assoc (X ◁ η) (f ▷ M.X)]

    -- 2. SWAP! A Left Whisker (◁) followed by a Right Whisker (▷)
    -- exchanges to pull `f` to the left: (f ▷ 𝟙_ C) ≫ (M.X ◁ η)
    rw [MonoidalCategory.whisker_exchange]
    simp only [Category.assoc]

    -- 3. Group the right unitor with the newly created (f ▷ 𝟙_ C).
    rw [← Category.assoc (ρ_ X).inv (f ▷ 𝟙_ C)]

    -- 4. Apply the naturality of the right unitor backwards!
    rw [← MonoidalCategory.rightUnitor_inv_naturality]
    simp only [Category.assoc]
    simp

variable (C)

/-- `list A` is a free monoid on the object `A` witnessed by the left adjoint of the forgetful functor from `Mon C` to `C`. -/
def freeMonForgetAdjunction : freeMon C ⊣ Mon.forget C :=
  Adjunction.mkOfHomEquiv {
    homEquiv (X : C) (Y : Mon C) := homEquiv X Y
    homEquiv_naturality_left_symm := by
     intros X X' M g h
     dsimp [homEquiv]
     congr
     dsimp [list.lift, list.foldr]
     rw [← plist.rc_uniq]
     · dsimp [list.map, plist.map]
       rw [← Category.assoc]
       simp only [plist.nil_rc]
     · dsimp [list.map, plist.map]
       rw [← Category.assoc, plist.cons_rc, Category.assoc]
       rw [Category.assoc, plist.cons_rc]
       simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
       refine X ◁ plist.rc plist.nil (g ▷ plist X' (𝟙_ C) ≫ plist.cons) ≫= ?_
       simp only [comp_whiskerRight, assoc]
       rw [Eq.symm (assoc (g ▷ plist X' (𝟙_ C))
          (X' ◁ plist.rc η (h ▷ M.X ≫ (μ : M.X ⊗ M.X ⟶ M.X))) (h ▷ M.X ≫ (μ : M.X ⊗ M.X ⟶ M.X)))]
       rw [Eq.symm (assoc (X ◁ plist.rc η
          (h ▷ M.X ≫ (μ : M.X ⊗ M.X ⟶ M.X))) (g ▷ M.X) (h ▷ M.X ≫ (μ : M.X ⊗ M.X ⟶ M.X)))]
       refine ?_ =≫ h ▷ M.X ≫ (μ : M.X ⊗ M.X ⟶ M.X)
       exact Eq.symm (whisker_exchange g (plist.rc η (h ▷ M.X ≫ (μ : M.X ⊗ M.X ⟶ M.X))))
    homEquiv_naturality_right f g := by
      dsimp [homEquiv]; rw [Category.assoc]
  }

section Monadicity

open Monad

instance hasReflexiveCoequalizersOfMon' : HasReflexiveCoequalizers (Mon C) where
  has_coeq {A B} (f g) := sorry

open CategoryTheory.Limits

instance hasReflexiveCoequalizersOfMon [HasReflexiveCoequalizers C] :
    HasReflexiveCoequalizers (Mon C) where
  -- THE FIX: Add [IsReflexivePair f g] to the binders!
  has_coeq {A B} f g [IsReflexivePair f g] := by

    -- 1. Port the reflexive pair instance from Mon C down to C
    haveI : IsReflexivePair f.hom g.hom := by
      obtain ⟨s, hf, hg⟩ : ∃ (s : B ⟶ A), s ≫ f = 𝟙 B ∧ s ≫ g = 𝟙 B := IsReflexivePair.common_section'
      exact ⟨⟨s.hom, by rw [← Mon.comp_hom', hf, Mon.id_hom'], by rw [← Mon.comp_hom', hg, Mon.id_hom']⟩⟩

    -- 2. Lean now natively sees `HasCoequalizer f.hom g.hom`
    exact HasColimit.mk {
      cocone :=
        let Q_X := coequalizer f.hom g.hom

        let q := coequalizer.π f.hom g.hom

        -- To define μ_Q, we factor the map (B.mul ≫ q) through the coequalizer of the tensors.
        -- We assume (q ⊗ₘ q) is the coequalizer of (f.hom ⊗ₘ f.hom) and (g.hom ⊗ₘ g.hom).
        let μ_Q : Q_X ⊗ Q_X ⟶ Q_X :=
          coequalizer.desc (B.mul ≫ q) (by
            -- Proof that (f.hom ⊗ f.hom) ≫ B.mul ≫ q = (g.hom ⊗ g.hom) ≫ B.mul ≫ q
            rw [← Category.assoc, ← Category.assoc]
            rw [IsMonHom.mul_hom f, IsMonHom.mul_hom g]
            simp only [Category.assoc]
            rw [coequalizer.condition f.hom g.hom])

        -- THE FIX: Define the MonObj instance locally so `Mon.mk` can find it!
        letI : MonObj Q_X := {
          one := η[B.X] ≫ q
          mul := μ_Q
          one_mul := by sorry
          mul_one := by sorry
          mul_assoc := by sorry
        }

        Cocone.mk (Mon.mk Q_X)
          { app := fun j => match j with
              -- Now we use Mon.Hom.mk' exclusively for the morphisms where it belongs!
              | WalkingParallelPair.zero => f ≫ Mon.Hom.mk' q (by sorry) (by sorry)
              | WalkingParallelPair.one  => Mon.Hom.mk' q (by sorry) (by sorry)
            naturality := by sorry }

      isColimit := {
        desc := fun s =>
          -- coequalizer.desc infers f.hom and g.hom from the type of the proof!
          -- Argument 1: The outgoing morphism (k)
          -- Argument 2: The proof that it coequalizes (w)
          Mon.Hom.mk' (coequalizer.desc (s.ι.app WalkingParallelPair.one).hom (by sorry))
            (by sorry)
            (by sorry)
        fac := by sorry
        uniq := by sorry
      }}

instance preservesColimitOfIsReflexivePairOfMonForget [HasReflexiveCoequalizers C] :
    PreservesColimitOfIsReflexivePair (Mon.forget C) where
  out {A B} f g r := {
    preserves := fun hc => {
      desc := fun s => coequalizer.desc f.hom g.hom s.ι.app.one
      fac := by sorry
      uniq := by sorry
    }
  }

instance preservesColimitOfIsReflexivePairOfMonForget' :
    PreservesColimitOfIsReflexivePair (Mon.forget C) where
  out {A B} (f g) r := sorry

instance monadicRightAdjointOfMonForget : MonadicRightAdjoint (Mon.forget C) :=
  monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms <| freeMonForgetAdjunction C

end Monadicity

def monad : Monad C :=
  freeMonForgetAdjunction C |> Adjunction.toMonad

end list

def monToListAlgebraFunctor : Mon C ⥤ (list.monad C).Algebra := Monad.comparison _

/-- The equivalence between the category of algebras for the `list` monad and the category of monoids in `C`. -/
instance monToListAlgebraFunctorIsEquivalence [ListArithmetic C] :
    (monToListAlgebraFunctor C).IsEquivalence := by
  refine MonadicRightAdjoint.eqv

namespace list

variable {C}

def join {A : C} : list (list A) ⟶ list A := (monad C).μ.app A

theorem join_nil {A : C} : list.nil ≫ list.join = list.nil (C:=C) (A:=A)  := by
  dsimp [list.join, monad, freeMonForgetAdjunction, homEquiv, lift, list.foldr]
  simp [nil, plist.nil_rc]
  rfl

theorem flatten_nil {A : C} : list.nil ≫ list.flatten = list.nil (C:=C) (A:=A) := by
  dsimp [list.flatten, list.rc, list, list.nil]
  simp only [plist.nil_rc]

--flatten (xs:xss) = xs ++ flatten xss
theorem flatten_cons {A : C} :
  list.cons ≫ list.flatten = (list A ◁ list.flatten (A:=A)) ≫ list.append (A:=A) := by
  dsimp [list.flatten, list.rc, list.cons]
  rw [plist.cons_rc]

theorem join_cons {A : C} : list.cons ≫ list.join = list A ◁ list.join (A:=A) ≫ list.append := by
  sorry

theorem join_eq_flatten {A : C} : list.join (A := A) = list.flatten := by
  dsimp [flatten,rc]
  apply plist.rc_uniq
  · rw [← join_nil, nil]
  · have := join_cons (A:=A)
    dsimp [cons] at this
    exact this

namespace Algebra

open Category

/-- A monoid structure on `A` gives rise to an algebra for the `list` monad. -/
@[simps!]
def ofMon (M : Mon C) : (monad C).Algebra := monToListAlgebraFunctor _ |>.obj M

@[simp]
theorem ofMon_a_eq {M : Mon C} : (ofMon M).a = list.lift (𝟙 M.X) := by
  dsimp [ofMon, monToListAlgebraFunctor, Monad.comparison]
  rfl

instance monClass (α : (monad C).Algebra) : MonObj α.A where
  one := nil ≫ α.a
  mul := (singleton ⊗ₘ singleton) ≫ append ≫ α.a
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry

def mon (α : (monad C).Algebra) : Mon C where
  X := α.A

noncomputable def monToListAlgebraFunctorIsEquivalence' : (monad C).Algebra ≌ Mon C :=
  (monToListAlgebraFunctor C).asEquivalence.symm

-- SH: an explicit and constructive/computable construction of the equivalence without rcourse to the monadicity theorem
def equivalenceMon : (monad C).Algebra ≌ Mon C where
  functor := {
    obj := mon
    map {α α'} f := Mon.Hom.mk' f.1 (by sorry) (by sorry)
    map_id X := rfl
    map_comp := by
      intros X Y Z f g; ext; rw [Monad.Algebra.comp_f, Mon.comp_hom'] }
  inverse := monToListAlgebraFunctor C
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

end Algebra

end list

namespace Mon

variable {C}

open list Algebra

def aggregator (M : Mon C) : list M.X ⟶ M.X := ofMon M |>.a

section aggregator

variable {M : Mon C}

theorem aggregator_one : η ≫ aggregator M = η := by
  exact lift_one

theorem aggregator_mul : μ ≫ aggregator M = (aggregator M ⊗ₘ aggregator M) ≫ μ := by
  exact lift_mul

theorem aggregator_singleton : list.singleton ≫ aggregator M = 𝟙 M.X := by
  dsimp [aggregator]
  have := ofMon_a_eq (C:=C) (M:=M)
  dsimp [ofMon, monToListAlgebraFunctor] at this
  rw [this]
  dsimp [list.singleton, lift, foldr]
  rw [assoc, assoc, cons, plist.cons_rc, list.nil]
  simp only [id_whiskerRight, id_comp, plist.whiskerLeft_nil_whiskerLeft_rc_assoc,
    MonObj.mul_one, Iso.inv_hom_id]

theorem aggregator_join {M : Mon C} :
  list.join ≫ aggregator M = (list.map <| aggregator M) ≫ aggregator M := by
    dsimp [list.join, aggregator]
    have := (Algebra.ofMon M).assoc
    dsimp [ofMon, monToListAlgebraFunctor] at *
    rw [this]; clear this
    refine _ ≫= ?_
    simp only

/-- Theorem: Aggregator is functorial. -/
theorem aggregator_map' {M' : Mon C} {f : M ⟶ M'} :
    map f.hom ≫ aggregator M' = aggregator M ≫ f.hom := by
  dsimp [aggregator]
  have := ((freeMonForgetAdjunction C)).counit.naturality (X:=M) (Y:=M') f
  dsimp [freeMon] at *
  dsimp [freeMon, homEquiv, lift,foldr,map, plist.map, plist.rc, Act.forget] at *
  dsimp [Adjunction.homEquiv] at *
  have h_nat_hom := congr_arg (fun f => f.hom) this
  simp at h_nat_hom
  rw [← h_nat_hom]
  simp only [assoc]

/-- Theorem: Aggregator is functorial. -/
theorem aggregator_map {M' : Mon C} {f : M.X ⟶ M'.X} :
    map f ≫ aggregator M' = aggregator M ≫ f := by
  sorry


end aggregator

end Mon

end CategoryTheory
