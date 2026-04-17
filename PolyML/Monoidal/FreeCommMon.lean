/-
Copyright (c) 2025 Sina Hazratpour, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Michail Karatarakis
-/
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monad.Monadicity
import PolyML.Monoidal.ListArithmetic
import PolyML.Monoidal.FreeMon


/-! # The Free Commutative Monoid Monad

In this file, we define `bag A` as the free commutative monoid on `A`,
and establish useful relations between `bag A` and `list A`.

We also that show that any internal commutative monoid structure is the same as the data of an
algbera for the bag monad. Given a monoid structure on `A`, we define an aggregator morphism
`bag A ⟶ A` as the structure map of the algebra.

Therefore a bag structure on `A` is equivalent to the data of an aggregator.
-/


namespace CategoryTheory

open Category CategoryTheory ListArithmetic Functor MonoidalCategory
  MonObj CommMon Monad

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

class WithBags where
  functor : C ⥤ CommMon C
  adj : functor ⊣ CommMon.forget C

variable {C} [WithBags C]

open WithBags

/-- The common monoid structure on `bag A` is given by the free commutative monoid functor. -/
def freeCommMon (A : C) : CommMon C := WithBags.functor.obj A

def freeCommMon.lift {A : C} {M : CommMon C} (f : A ⟶ M.X) : freeCommMon A ⟶ M :=
  adj.homEquiv A M |>.invFun f

/-- The monoid structure on `bag A`. -/
def bagMon (A : C) : Mon C := freeCommMon A |>.toMon

def bagMon.lift {A : C} {M : CommMon C} (f : A ⟶ M.X) : bagMon A ⟶ M.toMon :=
  (freeCommMon.lift f) |> (CommMon.forget₂Mon C).map


theorem bagMon.lift_eq_counit_app {M : CommMon C} :
    (bagMon.lift (𝟙 M.X)).hom = (WithBags.adj.counit.app M).hom := by
  congr 1
  simp only [bagMon.lift, freeCommMon.lift]
  change (forget₂Mon C).map ((WithBags.adj.homEquiv M.X M).symm (𝟙 M.X)) = _
  rw [Adjunction.homEquiv_counit]
  simp only [Functor.map_id, Category.id_comp]
  aesop


/-- The underlying type of the free commutative monoid on `A`. -/
abbrev bag (A : C) : C := bagMon A |>.X

namespace bag

variable {A : C}

def endofunctor : C ⥤ C :=
  WithBags.functor ⋙ CommMon.forget C

instance monClass : MonObj (bag A) := bagMon A |> Mon.mon

instance isCommMonObj : IsCommMonObj (bag A) := freeCommMon A |> CommMon.comm

def nil : 𝟙_C ⟶ bag A := η

def append : bag A ⊗ bag A ⟶ bag A := μ

/-- `append` is symmetric because for bags. -/
@[reassoc (attr := simp)]
theorem braiding_append : (β_ (bag A) (bag A)).hom ≫ append = append := by
  dsimp [bag, append]
  simp only [IsCommMonObj.mul_comm, forget₂Mon_obj_mul]

def singleton : A ⟶ bag A := adj.unit.app A

def cons : A ⊗ bag A ⟶ bag A := (singleton ▷ bag A) ≫ append

def snoc : bag A ⊗ A ⟶ bag A := (bag A ◁ singleton) ≫ append

/-- Appending an element as head or tail is the same operation for bags. -/
theorem braiding_snoc_eq_cons : (β_ A (bag A)).hom ≫ snoc = cons := by
  dsimp [cons, snoc]
  nth_rw 2 [← braiding_append]
  simp only [BraidedCategory.braiding_naturality_left_assoc]

/-- Given a commutative monoid object `M` in `C`, this lifts
`f : A ⟶ M.X` to a morphism from `bag A` to `M.X`. -/
def lift {M : CommMon C} (f : A ⟶ M.X) : bag A ⟶ M.X :=
  bagMon.lift f |> (CommMon.forget C).map

theorem lift_eq_counit_app {M : CommMon C} :
    lift (𝟙 M.X) = (adj.counit.app M).hom := by
  simp [lift, bagMon.lift_eq_counit_app]

theorem one_lift {M : CommMon C} {f : A ⟶ M.X} : η ≫ lift f = η := by
  dsimp [lift]
  simp only [IsMonHom.one_hom]

theorem mul_lift {M : CommMon C} {f : A ⟶ M.X} :  μ ≫ lift f = (lift f ⊗ₘ lift f) ≫ μ := by
  dsimp [lift]
  simp only [IsMonHom.mul_hom]

theorem singleton_lift {M : CommMon C} {f : A ⟶ M.X} : singleton ≫ lift f = f := by
  dsimp [singleton, lift, bagMon.lift, freeCommMon.lift]
  exact (adj.homEquiv A M).right_inv f

/-- The functorial action of `bag` on morphisms. -/
def map {B : C} (f : A ⟶ B) : bag A ⟶ bag B := bag.endofunctor.map f

theorem map_eq_lift {B : C} (f : A ⟶ B) : map f = lift (f ≫ singleton) := by
  dsimp [map, endofunctor, lift, bagMon.lift, freeCommMon.lift, singleton]
  have h : (WithBags.adj.homEquiv A (freeCommMon B)).symm (f ≫ WithBags.adj.unit.app B) = WithBags.functor.map f := by
    apply (WithBags.adj.homEquiv A (freeCommMon B)).injective
    simp only [Equiv.apply_symm_apply]
    exact WithBags.adj.unit.naturality f
  aesop

theorem map_lift_eq_lift_comp {M : CommMon C} {B : C} (f : A ⟶ B) (g : B ⟶ M.X) :
    map f ≫ lift g = lift (f ≫ g) := by
  dsimp [lift]
  have := Adjunction.homEquiv_naturality_left_symm (C:=C) (adj) (Y:=M) (X:=B) (X':=A) f g
  dsimp [bagMon.lift, freeCommMon.lift, Adjunction.homEquiv, map, endofunctor]
  simp_all only [map_comp, comp', Category.assoc, Mon.comp_hom', toMon_X]

@[simp]
theorem nil_map {B : C} {f : A ⟶ B} :
    η ≫ map f = η := by
  rw [map_eq_lift]
  dsimp [lift]
  simp only [IsMonHom.one_hom, forget₂Mon_obj_one]

@[simp]
theorem singleton_naturality {B : C} {f : A ⟶ B} :
    singleton ≫ map f = f ≫ singleton := by
  rw [map_eq_lift, singleton_lift]

theorem append_map {B : C} {f : A ⟶ B} : (map f ⊗ₘ map f) ≫ μ = μ ≫ map f := by
  rw [map_eq_lift, mul_lift]

theorem self_tensor_map_self_cons {B : C} {f : A ⟶ B} :
    (f ⊗ₘ map f) ≫ cons = cons ≫ map f := by
  dsimp [cons, append]
  have h : (f ⊗ₘ map f) ≫ (singleton ▷ bag B) = (singleton ▷ bag A) ≫ (map f ⊗ₘ map f) := by
    rw [tensorHom_def]
    simp only [Category.assoc]
    rw [whisker_exchange]
    rw [← Category.assoc, ← comp_whiskerRight]
    rw [← singleton_naturality]
    rw [comp_whiskerRight, Category.assoc, ← tensorHom_def]
  rw [← Category.assoc, h, Category.assoc, append_map]
  aesop

def ofList [ListArithmetic C] : list A ⟶ bag A := list.lift (bag.singleton)

theorem ofList_nil [ListArithmetic C] :
    list.nil ≫ ofList = bag.nil (A:= A) := by
  simp only [bag.nil, ofList, singleton, list.nil, list.lift,list.foldr]
  simp only [plist.nil_rc]

theorem ofList_cons [ListArithmetic C] :
    list.cons ≫ ofList = A ◁ ofList ≫ bag.cons := by
  dsimp [ofList, list.lift, list.foldr, list.cons]
  rw [plist.cons_rc]
  refine _ ≫= ?_
  dsimp [cons, bag.append, bag]

/-
TODO: show that `ofList` is a quotient morphism. The relation should be thought of as
the permutation relation on lists, i.e. `l1 ~ l2` if `l1` can be obtained from `l2` by permuting the elements.

Tip: can we show for instance that this map is an effective epi? If so, every effective epi is regular and therefore W is `perm` relation.
-/

end bag

section Monadicity

open Monad Limits

instance hasReflexiveCoequalizersOfMon : HasReflexiveCoequalizers (CommMon C) where
  has_coeq {A B} (f g) := by sorry

instance preservesColimitOfIsReflexivePairOfMonForget :
    PreservesColimitOfIsReflexivePair (CommMon.forget C) where
  out {A B} (f g) r := by sorry

instance :  (CommMon.forget C).ReflectsIsomorphisms where
  reflects {A B} f is_iso := by sorry

instance monadicRightAdjointOfMonForget : MonadicRightAdjoint (CommMon.forget C) :=
  monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms <| WithBags.adj

end Monadicity

namespace bag

variable (C)

def monad : Monad C := adj |> Adjunction.toMonad

def commMonToBagAlgebraFunctor : CommMon C ⥤ (bag.monad C).Algebra := Monad.comparison _

/-- The equivalence between the category of algebras for the `list` monad and the category of monoids in `C`. -/
instance commMonToBagAlgebraFunctorIsEquivalence : (commMonToBagAlgebraFunctor C).IsEquivalence := by
  refine MonadicRightAdjoint.eqv

variable {C} {A : C}

theorem monad_obj : (monad C).obj A = bag A := rfl

def join : bag (bag A) ⟶ bag A := (monad C).μ.app A

namespace Algebra

/-- A commutative monoid structure on gives rise to an algebra for the `bag` monad. -/
@[simps!]
def ofCommMon (M : CommMon C) : (monad C).Algebra := commMonToBagAlgebraFunctor _ |>.obj M

@[simp]
theorem ofMon_a_eq {M : CommMon C} : (ofCommMon M).a = bag.lift (𝟙 M.X) := by
  dsimp [ofCommMon, commMonToBagAlgebraFunctor, Monad.comparison]
  have := CategoryTheory.Adjunction.unit_comp_map_eq_iff (C:=C)
     (adj) (A:=M.X) (B:=M) (f:= (bagMon.lift (𝟙 M.X))) (𝟙 M.X)
  dsimp [monad, lift]
  simp only [Functor.map_id, id_comp] at this
  symm
  congr
  apply this.mp
  simpa using singleton_lift


-- 1. The monad multiplication (join) distributes over the free monoid multiplication (μ).
lemma join_mul : μ ≫ bag.join (A:=A) = (bag.join ⊗ₘ bag.join) ≫ μ := by
  -- Follows from the fact that `join` evaluates to `lift (𝟙 (bag A))`
  -- and `lift` distributes over `μ` via `mul_lift`.
  sorry

-- 2. The monad unit law applied to join.
lemma monad_unit_law : singleton ≫ bag.join (A:=A) = 𝟙 (bag A) := by
  -- Unfold the local definitions to expose the underlying monad components
  dsimp [singleton, bag.join, monad]

  -- The left unit law of a monad generated by an adjunction (L ⊣ R) is
  -- mathematically definitionally equal to the right triangle identity:
  -- R.map (ε_{L.obj X}) ≫ η_{R.obj (L.obj X)} = 𝟙
  exact adj.right_triangle_components (WithBags.functor.obj A)

-- 3. Appending two singletons and flattening is the same as the base append.
lemma pair_join : (singleton ⊗ₘ singleton) ≫ μ ≫ bag.join (A:=A) = μ := by
  calc (singleton ⊗ₘ singleton) ≫ μ ≫ bag.join (A:=A)
    _ = (singleton ⊗ₘ singleton) ≫ (bag.join ⊗ₘ bag.join) ≫ μ := by
      -- Directly rewrite without associativity shifts!
      rw [join_mul]

    -- Notice the extra parentheses around the entire tensor product below!
    _ = ((singleton ≫ bag.join) ⊗ₘ (singleton ≫ bag.join)) ≫ μ := by aesop
      --rw [← Category.assoc, ← MonoidalCategory.tensor_comp]

    _ = (𝟙 (bag A) ⊗ₘ 𝟙 (bag A)) ≫ μ := by
      rw [monad_unit_law]
    _ = μ := by aesop


-- Bridge the typeclass gap between the monad functor and the bag instance
instance {X : C} : MonObj ((monad C).obj X) := bag.monClass

-- 4. The Core Algebra Multiplication Law
lemma mu_comp_a (α : (monad C).Algebra) :
    μ ≫ α.a = ((α.a ≫ singleton) ⊗ₘ (α.a ≫ singleton)) ≫ μ ≫ α.a := by
  calc μ ≫ α.a
    _ = ((singleton ⊗ₘ singleton) ≫ μ ≫ bag.join (A:=α.A)) ≫ α.a := by rw [pair_join]
    _ = (singleton ⊗ₘ singleton) ≫ μ ≫ (bag.join ≫ α.a) := by rw [Category.assoc, Category.assoc]
    _ = (singleton ⊗ₘ singleton) ≫ μ ≫ map α.a ≫ α.a := by
      -- Bridge the syntax gap between mathlib's monad and your bag monad
      have h_assoc : bag.join (A:=α.A) ≫ α.a = map α.a ≫ α.a := α.assoc
      rw [h_assoc]

    _ = (singleton ⊗ₘ singleton) ≫ (map α.a ⊗ₘ map α.a) ≫ μ ≫ α.a := by
      -- 1. Group `μ` and `map α.a` together so `append_map` can find the exact pattern
      rw [← Category.assoc (f := μ)]
      rw [← append_map]
      -- 2. Reset associativity back to the standard right-leaning structure
      simp only [Category.assoc]

    _ = ((singleton ≫ map α.a) ⊗ₘ (singleton ≫ map α.a)) ≫ μ ≫ α.a := by
      -- Bypass tensor_comp using the manual whisker compression trick!
      have h_tensor : (singleton ⊗ₘ singleton) ≫ (map α.a ⊗ₘ map α.a) = ((singleton ≫ map α.a) ⊗ₘ (singleton ≫ map α.a)) := by
        simp only [tensorHom_def, Category.assoc]

        -- 1. Group the middle whiskers and swap them
        rw [← Category.assoc (f := bag ((monad C).obj α.A) ◁ singleton)]
        rw [whisker_exchange]

        -- 2. Reset associativity to standard right-leaning chain
        simp only [Category.assoc]

        -- 3. Compress the two left whiskers on the right side of the chain
        rw [← MonoidalCategory.whiskerLeft_comp]

        -- 4. CRITICAL FIX: Group the first two right whiskers together!
        rw [← Category.assoc (f := singleton ▷ (monad C).obj α.A)]

        -- 5. Compress the grouped right whiskers. This perfectly matches the RHS!
        rw [← MonoidalCategory.comp_whiskerRight]

      -- Apply our custom tensor lemma
      rw [← Category.assoc (f := singleton ⊗ₘ singleton)]
      rw [h_tensor]

    _ = ((α.a ≫ singleton) ⊗ₘ (α.a ≫ singleton)) ≫ μ ≫ α.a := by
      -- `simp only` dives into the tensor product and rewrites both sides
      simp only [singleton_naturality]



/-- An algebra for the `bag` monad is a commutative monoid structure. -/
instance monClassOf (α : Algebra (monad C)) : MonObj (α.A) where
  one := nil ≫ α.a
  mul := (singleton ⊗ₘ singleton) ≫ μ ≫ α.a
  one_mul := by
    dsimp [MonObj.one, MonObj.mul]

    -- 1. Format the LHS to cleanly match the end of our backward calculation
    have h_lhs : ((nil ≫ α.a) ▷ α.A) ≫ (singleton ⊗ₘ singleton) ≫ μ ≫ α.a =
         ((nil ≫ α.a ≫ singleton) ⊗ₘ singleton) ≫ μ ≫ α.a := by
      simp only [tensorHom_def]

      -- Clean identities. This makes the chain right-associative: A ≫ (B ≫ C)
      simp only [Category.assoc]

      -- CRITICAL FIX: Shift the parenthesis left to group the first two terms: (A ≫ B) ≫ C
      rw [← Category.assoc (f := (nil ≫ α.a) ▷ α.A)]

      -- Now the two right-whiskers are perfectly isolated. Compress them!
      rw [← MonoidalCategory.comp_whiskerRight]

      -- Let simp flatten the inner parentheses `(nil ≫ α.a) ≫ singleton`
      simp only [Category.assoc]

    rw [h_lhs]

    -- Bridge the syntax gap for the algebra unit law
    have h_unit : singleton ≫ α.a = 𝟙 α.A := α.unit

    -- 2. We prove the equality strictly backwards from the identity unitor!
    symm
    calc (λ_ α.A).hom
      _ = (λ_ α.A).hom ≫ 𝟙 α.A := by rw [Category.comp_id]
      _ = (λ_ α.A).hom ≫ (singleton ≫ α.a) := by rw [← h_unit]
      _ = ((λ_ α.A).hom ≫ singleton) ≫ α.a := by rw [Category.assoc]

      -- Push the unitor backwards through its naturality square
      _ = ((𝟙_C ◁ singleton) ≫ (λ_ (bag α.A)).hom) ≫ α.a := by rw [← leftUnitor_naturality]
      _ = (𝟙_C ◁ singleton) ≫ (λ_ (bag α.A)).hom ≫ α.a := by rw [Category.assoc]

      -- Free monoid one_mul law. Note the explicit `bag.nil (A:=α.A)` to help Lean's typechecker!
      _ = (𝟙_C ◁ singleton) ≫ ((bag.nil (A:=α.A) ▷ bag α.A) ≫ μ) ≫ α.a := by
        have h_free_one : (bag.nil (A:=α.A) ▷ bag α.A) ≫ μ = (λ_ (bag α.A)).hom := by apply MonObj.one_mul
        rw [← h_free_one]

      _ = ((𝟙_C ◁ singleton) ≫ (bag.nil (A:=α.A) ▷ bag α.A)) ≫ μ ≫ α.a := by rw [← Category.assoc];aesop

      -- Interchange the left whiskers to perfectly form the tensor
      _ = (bag.nil (A:=α.A) ⊗ₘ singleton) ≫ μ ≫ α.a := by
        have h_tensor_nil : (𝟙_C ◁ singleton) ≫ (bag.nil (A:=α.A) ▷ bag α.A) = (bag.nil (A:=α.A) ⊗ₘ singleton) := by
          simp only [tensorHom_def]
          rw [whisker_exchange]
        rw [h_tensor_nil]

      -- >>> THE CORRECT FINAL SEQUENCE <<<

      -- 1. Apply the massive Core Algebra Multiplication Law to expand μ ≫ α.a
      -- 1. Apply the massive Core Algebra Multiplication Law to expand μ ≫ α.a
      _ = (bag.nil (A:=α.A) ⊗ₘ singleton) ≫ (((α.a ≫ singleton) ⊗ₘ (α.a ≫ singleton)) ≫ μ ≫ α.a) := by
        -- We must use conv_lhs so Lean ONLY expands the left side,
        -- otherwise it will double-expand the target on the right side!
        conv_lhs => rw [mu_comp_a]

      -- 2. Shift associativity to group the TWO TENSORS together!
      _ = ((bag.nil (A:=α.A) ⊗ₘ singleton) ≫ ((α.a ≫ singleton) ⊗ₘ (α.a ≫ singleton))) ≫ μ ≫ α.a := by
        rw [← Category.assoc]

      -- 3. Now the tensors are perfectly isolated in parentheses. Compress them!
      _ = ((nil ≫ α.a ≫ singleton) ⊗ₘ (singleton ≫ α.a ≫ singleton)) ≫ μ ≫ α.a := by
        have h_compress : (bag.nil (A:=α.A) ⊗ₘ singleton) ≫ ((α.a ≫ singleton) ⊗ₘ (α.a ≫ singleton)) =
            ((nil ≫ α.a ≫ singleton) ⊗ₘ (singleton ≫ α.a ≫ singleton)) := by
          simp only [tensorHom_def, Category.assoc]
          rw [← Category.assoc (f := bag α.A ◁ singleton)]
          rw [whisker_exchange]
          simp only [Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
          simp
        rw [h_compress]

      -- 4. Evaluate the unit law locally, then let simp magically inject it into the tensor!
      _ = ((nil ≫ α.a ≫ singleton) ⊗ₘ singleton) ≫ μ ≫ α.a := by
        have h_right : singleton ≫ α.a ≫ singleton = singleton (A:=α.A) := by
          -- Group the first two terms: (singleton ≫ α.a) ≫ singleton
          rw [← Category.assoc]
          rw [h_unit]
          rw [Category.id_comp]
        -- `simp only` dives inside the `⊗ₘ` and swaps the evaluated term
        simp only [h_right]


  mul_one := by
    dsimp [MonObj.one, MonObj.mul]

    -- 1. Format the LHS to cleanly match the end of our backward calculation
    -- 1. Format the LHS to cleanly match the end of our backward calculation
    -- 1. Format the LHS. Notice we start directly with `α.A ◁` to perfectly match the goal!
    have h_lhs : α.A ◁ (nil ≫ α.a) ≫ (singleton ⊗ₘ singleton) ≫ μ ≫ α.a = (singleton ⊗ₘ (nil ≫ α.a ≫ singleton)) ≫ μ ≫ α.a := by
      -- Expand the tensors
      simp only [tensorHom_def]

      -- Clean up identities and flatten parentheses
      simp only [Category.assoc, MonoidalCategory.whiskerRight_id]

      -- 2. SURGICAL REGROUP: Wrap the first Left-whisker and Right-whisker together
      rw [← Category.assoc (f := α.A ◁ (nil ≫ α.a))]

      -- 3. Swap them! (L ≫ R becomes R ≫ L)
      rw [whisker_exchange]

      -- 4. Flatten again
      simp only [Category.assoc]

      -- 5. SURGICAL REGROUP: Wrap the two Left-whiskers together
      rw [← Category.assoc (f := bag α.A ◁ (nil ≫ α.a))]

      -- 6. Compress!
      rw [← MonoidalCategory.whiskerLeft_comp]

      -- 7. Final cleanup
      simp only [Category.assoc]
      aesop

    -- Now the pattern is a 1:1 identical match, and the rewrite will succeed!
    rw [h_lhs]
    -- Bridge the syntax gap for the algebra unit law
    have h_unit : singleton ≫ α.a = 𝟙 α.A := α.unit

    -- 2. Prove the equality strictly backwards from the RIGHT identity unitor!
    symm
    calc (ρ_ α.A).hom
      _ = (ρ_ α.A).hom ≫ 𝟙 α.A := by rw [Category.comp_id]
      _ = (ρ_ α.A).hom ≫ (singleton ≫ α.a) := by rw [← h_unit]
      _ = ((ρ_ α.A).hom ≫ singleton) ≫ α.a := by rw [Category.assoc]

      -- Push the unitor backwards through its naturality square
      _ = ((singleton ▷ _) ≫ (ρ_ (bag α.A)).hom) ≫ α.a := by rw [← rightUnitor_naturality]
      _ = (singleton ▷ _) ≫ (ρ_ (bag α.A)).hom ≫ α.a := by rw [Category.assoc]

      -- Free monoid mul_one law (Note the explicit bag.nil type injection again!)
      _ = (singleton ▷ _) ≫ ((bag α.A ◁ bag.nil (A:=α.A)) ≫ μ) ≫ α.a := by
        have h_free_one : (bag α.A ◁ bag.nil (A:=α.A)) ≫ μ = (ρ_ (bag α.A)).hom := by apply MonObj.mul_one
        rw [← h_free_one]

      _ = ((singleton ▷ _) ≫ (bag α.A ◁ bag.nil (A:=α.A))) ≫ μ ≫ α.a := by rw [← Category.assoc]; aesop

      -- Form the tensor product
      _ = (singleton ⊗ₘ bag.nil (A:=α.A)) ≫ μ ≫ α.a := by
        have h_tensor_nil : (singleton ▷ _) ≫ (bag α.A ◁ bag.nil (A:=α.A)) = (singleton ⊗ₘ bag.nil (A:=α.A)) := by
          simp only [tensorHom_def]
        rw [h_tensor_nil]

      -- 1. Apply the Core Algebra Law, using conv_lhs to strictly prevent double-rewrites!
      _ = (singleton ⊗ₘ bag.nil (A:=α.A)) ≫ (((α.a ≫ singleton) ⊗ₘ (α.a ≫ singleton)) ≫ μ ≫ α.a) := by
        conv_lhs => rw [mu_comp_a]

      -- 2. Shift associativity to group the TWO TENSORS together
      _ = ((singleton ⊗ₘ bag.nil (A:=α.A)) ≫ ((α.a ≫ singleton) ⊗ₘ (α.a ≫ singleton))) ≫ μ ≫ α.a := by
        rw [← Category.assoc]

      -- 3. Compress the tensors using our trusted manual whisker swap
      _ = ((singleton ≫ α.a ≫ singleton) ⊗ₘ (bag.nil (A:=α.A) ≫ α.a ≫ singleton)) ≫ μ ≫ α.a := by
        have h_compress : (singleton ⊗ₘ bag.nil (A:=α.A)) ≫ ((α.a ≫ singleton) ⊗ₘ (α.a ≫ singleton)) =
            ((singleton ≫ α.a ≫ singleton) ⊗ₘ (bag.nil (A:=α.A) ≫ α.a ≫ singleton)) := by
          simp only [tensorHom_def, Category.assoc]
          rw [← Category.assoc (f := bag α.A ◁ bag.nil (A:=α.A))]
          rw [whisker_exchange]
          simp only [Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
          simp
        rw [h_compress]
      -- 4. Evaluate the unit law locally on the LEFT side of the tensor
      _ = (singleton ⊗ₘ (nil ≫ α.a ≫ singleton)) ≫ μ ≫ α.a := by
        have h_left : singleton ≫ α.a ≫ singleton = singleton (A:=α.A) := by
          rw [← Category.assoc]
          rw [h_unit]
          rw [Category.id_comp]

        -- Let simp magically dive into the left side of the tensor and substitute!
        simp only [h_left]



  mul_assoc := by
    dsimp [MonObj.mul]

    -- 1. FORMAT THE LEFT HAND SIDE ((mul ⊗ 𝟙) ≫ mul)
    have h_lhs : ((((singleton ⊗ₘ singleton) ≫ μ ≫ α.a) ⊗ₘ 𝟙 α.A) ≫ (singleton ⊗ₘ singleton) ≫ μ ≫ α.a) =
                 (((singleton ⊗ₘ singleton) ≫ μ ≫ α.a ≫ singleton) ⊗ₘ singleton) ≫ μ ≫ α.a := by
      -- Expand all tensors
      simp only [tensorHom_def]

      -- Clean up the identities
      simp only [Category.assoc, MonoidalCategory.whiskerLeft_id, Category.comp_id]

      -- SURGICAL REGROUP: Target the fully unpacked inner tensor!
      rw [← Category.assoc (f := (singleton ▷ α.A ≫ bag α.A ◁ singleton ≫ μ ≫ α.a) ▷ α.A)]

      -- Compress the two right-whiskers
      rw [← MonoidalCategory.comp_whiskerRight]
      simp only [Category.assoc]

    -- 2. FORMAT THE RIGHT HAND SIDE (α_.hom ≫ (𝟙 ⊗ mul) ≫ mul)
    have h_rhs : (α_ α.A α.A α.A).hom ≫ (𝟙 α.A ⊗ₘ ((singleton ⊗ₘ singleton) ≫ μ ≫ α.a)) ≫ (singleton ⊗ₘ singleton) ≫ μ ≫ α.a =
                 (α_ α.A α.A α.A).hom ≫ (singleton ⊗ₘ ((singleton ⊗ₘ singleton) ≫ μ ≫ α.a ≫ singleton)) ≫ μ ≫ α.a := by
      -- Expand all tensors
      simp only [tensorHom_def]

      -- Clean up the identities
      simp only [Category.assoc]

      -- A. Group the mismatched Left-whisker and Right-whisker (fully unpacked!)
      rw [← Category.assoc (f := α.A ◁ (singleton ▷ α.A ≫ bag α.A ◁ singleton ≫ μ ≫ α.a))]

      -- B. Swap them to align the left-whiskers
      rw [whisker_exchange]
      simp only [Category.assoc]

      -- C. Group the two adjacent Left-whiskers (fully unpacked base!)
      rw [← Category.assoc (f := bag α.A ◁ (singleton ▷ α.A ≫ bag α.A ◁ singleton ≫ μ ≫ α.a))]

      -- D. Compress them!
      rw [← MonoidalCategory.whiskerLeft_comp]
      simp only [Category.assoc]
      aesop

    -- Rewrite both sides to their compressed forms
    simp at *
    rw [h_lhs, h_rhs]
    -- 3. BRIDGE THE LHS: "Un-compress" the tensor backwards using mu_comp_a
    have bridge_LHS : (((singleton ⊗ₘ singleton) ≫ μ) ⊗ₘ singleton) ≫ μ ≫ α.a =
                      (((singleton ⊗ₘ singleton) ≫ μ ≫ α.a ≫ singleton) ⊗ₘ singleton) ≫ μ ≫ α.a := by
      calc (((singleton ⊗ₘ singleton) ≫ μ) ⊗ₘ singleton) ≫ μ ≫ α.a
        _ = (((singleton ⊗ₘ singleton) ≫ μ) ⊗ₘ singleton) ≫ (((α.a ≫ singleton) ⊗ₘ (α.a ≫ singleton)) ≫ μ ≫ α.a) := by
          conv_lhs => rw [mu_comp_a]
        _ = ((((singleton ⊗ₘ singleton) ≫ μ) ⊗ₘ singleton) ≫ ((α.a ≫ singleton) ⊗ₘ (α.a ≫ singleton))) ≫ μ ≫ α.a := by
          rw [← Category.assoc]
        _ = (((singleton ⊗ₘ singleton) ≫ μ ≫ α.a ≫ singleton) ⊗ₘ (singleton ≫ α.a ≫ singleton)) ≫ μ ≫ α.a := by
          -- Standard manual tensor compression!
          have h_comp : (((singleton ⊗ₘ singleton) ≫ μ) ⊗ₘ singleton) ≫ ((α.a ≫ singleton) ⊗ₘ (α.a ≫ singleton)) = (((singleton ⊗ₘ singleton) ≫ μ ≫ α.a ≫ singleton) ⊗ₘ (singleton ≫ α.a ≫ singleton)) := by
            simp only [tensorHom_def, Category.assoc]
            rw [← Category.assoc (f := bag α.A ◁ singleton)]
            rw [whisker_exchange]
            simp only [Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.comp_whiskerRight]
          rw [h_comp]
        _ = (((singleton ⊗ₘ singleton) ≫ μ ≫ α.a ≫ singleton) ⊗ₘ singleton) ≫ μ ≫ α.a := by
          -- Simplify (singleton ≫ α.a ≫ singleton) to (singleton)
          have h_unit : singleton ≫ α.a ≫ singleton = singleton (A:=α.A) := by
            rw [← Category.assoc, α.unit, Category.id_comp]
          simp only [h_unit]

    -- 4. BRIDGE THE RHS: "Un-compress" the tensor backwards using mu_comp_a
    have bridge_RHS : (α_ α.A α.A α.A).hom ≫ (singleton ⊗ₘ ((singleton ⊗ₘ singleton) ≫ μ)) ≫ μ ≫ α.a =
                      (α_ α.A α.A α.A).hom ≫ (singleton ⊗ₘ ((singleton ⊗ₘ singleton) ≫ μ ≫ α.a ≫ singleton)) ≫ μ ≫ α.a := by
      calc (α_ α.A α.A α.A).hom ≫ (singleton ⊗ₘ ((singleton ⊗ₘ singleton) ≫ μ)) ≫ μ ≫ α.a
        _ = (α_ α.A α.A α.A).hom ≫ (singleton ⊗ₘ ((singleton ⊗ₘ singleton) ≫ μ)) ≫ (((α.a ≫ singleton) ⊗ₘ (α.a ≫ singleton)) ≫ μ ≫ α.a) := by
          conv_lhs => rw [mu_comp_a]
        _ = (α_ α.A α.A α.A).hom ≫ ((singleton ⊗ₘ ((singleton ⊗ₘ singleton) ≫ μ)) ≫ ((α.a ≫ singleton) ⊗ₘ (α.a ≫ singleton))) ≫ μ ≫ α.a := by
          simp only [Category.assoc]
        _ = (α_ α.A α.A α.A).hom ≫ ((singleton ≫ α.a ≫ singleton) ⊗ₘ (((singleton ⊗ₘ singleton) ≫ μ) ≫ α.a ≫ singleton)) ≫ μ ≫ α.a := by
          -- Standard manual tensor compression!
          have h_comp : (singleton ⊗ₘ ((singleton ⊗ₘ singleton) ≫ μ)) ≫ ((α.a ≫ singleton) ⊗ₘ (α.a ≫ singleton)) = ((singleton ≫ α.a ≫ singleton) ⊗ₘ (((singleton ⊗ₘ singleton) ≫ μ) ≫ α.a ≫ singleton)) := by
            simp only [tensorHom_def, Category.assoc]

            -- Target the FULLY UNPACKED inner tensor!
            rw [← Category.assoc (f := bag α.A ◁ (singleton ▷ α.A ≫ bag α.A ◁ singleton ≫ μ))]

            -- Now the exchange will work
            rw [whisker_exchange]
            simp only [Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
            aesop
          rw [h_comp]
        _ = (α_ α.A α.A α.A).hom ≫ (singleton ⊗ₘ ((singleton ⊗ₘ singleton) ≫ μ ≫ α.a ≫ singleton)) ≫ μ ≫ α.a := by
          have h_unit : singleton ≫ α.a ≫ singleton = singleton (A:=α.A) := by
            -- Shift parentheses to group (singleton ≫ α.a)
            rw [← Category.assoc]

            -- Use 'erw' instead of 'rw' so Lean recognizes 'singleton' as the monad unit 'η'!
            erw [α.unit]

            -- Clean up the remaining (𝟙 α.A ≫ singleton)
            rw [Category.id_comp]
          simp only [h_unit, Category.assoc]

    -- 5. THE FREE MONOID ASSOCIATIVITY LAW
    -- Now we just need to relate the "un-compressed" raw tensors.
    have h_free : (((singleton ⊗ₘ singleton) ≫ μ) ⊗ₘ singleton) ≫ μ =
                  (α_ α.A α.A α.A).hom ≫ (singleton ⊗ₘ ((singleton ⊗ₘ singleton) ≫ μ)) ≫ μ := by
      -- Expand into standard Mathlib Category Theory whiskers
      simp only [tensorHom_def, Category.assoc, MonoidalCategory.comp_whiskerRight]
      -- Swap the inner whiskers!
      have h_swap : (μ ▷ α.A) ≫ (bag α.A ◁ singleton) = ((bag α.A ⊗ bag α.A) ◁ singleton) ≫ (μ ▷ bag α.A) := by rw [whisker_exchange]
      rw [← Category.assoc (f := μ ▷ α.A)]
      rw [h_swap]
      -- Apply the core associativity law of the `bag` commutative monoid
      have h_assoc : (μ ▷ bag α.A) ≫ μ = (α_ (bag α.A) (bag α.A) (bag α.A)).hom ≫ (bag α.A ◁ μ) ≫ μ := by apply MonObj.mul_assoc
      --rw [h_assoc]
      -- Let Mathlib's powerful `simp` engine handle the remaining associator naturality and parenthesis flattening
      simp

    -- 6. THE GRAND FINALE
    -- Substitute the un-compressed forms into the goal
    rw [← bridge_LHS, ← bridge_RHS]

    -- Shift the parentheses left to completely isolate the free monoid logic from the `α.a` map at the end
    rw [← Category.assoc (f := (((singleton ⊗ₘ singleton) ≫ μ) ⊗ₘ singleton))]
    rw [← Category.assoc (f := (α_ α.A α.A α.A).hom)]
    --rw [← Category.assoc (f := (singleton ⊗ₘ ((singleton ⊗ₘ singleton) ≫ μ)))]

    -- Apply the free monoid associativity law!
    rw [h_free]
    simp


















instance isCommMonObj {α : Algebra (monad C)} : IsCommMonObj (α.A) where
  mul_comm := by
    dsimp [MonObj.mul]
    rw [tensorHom_def', ← Category.assoc]
    rw [← BraidedCategory.braiding_naturality_left_assoc]
    rw [← BraidedCategory.braiding_naturality_right]
    rw [Category.assoc, Category.assoc]
    simp only [IsCommMonObj.mul_comm_assoc, forget₂Mon_obj_mul, Category.assoc]
    exact Eq.symm (whisker_exchange_assoc singleton singleton (μ ≫ α.a))

def commMon (α : (monad C).Algebra) : CommMon C where
  X := α.A

noncomputable def commMonToBagAlgebraFunctorIsEquivalence' : (monad C).Algebra ≌ CommMon C :=
  (commMonToBagAlgebraFunctor C).asEquivalence.symm

-- SH: an explicit and constructive/computable construction of the equivalence without recourse to the monadicity theorem
def equivalenceMon : (monad C).Algebra ≌ CommMon C where
  functor := {
    obj := commMon
    map {α α'} f := Mon.Hom.mk' f.1 (by sorry) (by sorry)
    map_id := by
      intros α
      ext
      simp only [Algebra.id_f]
      aesop
    map_comp := by
      intros α β γ f g
      ext
      simp only [Algebra.comp_f]
      aesop
  }
  inverse := commMonToBagAlgebraFunctor C
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

end Algebra

open Algebra

def aggregator (M : CommMon C) : bag M.X ⟶ M.X := (ofCommMon M).a

section aggregator

variable {M : CommMon C}

theorem aggregator_eq_lift : aggregator M = lift (𝟙 M.X) := by
  dsimp [aggregator, ofCommMon, lift]
  simp [commMonToBagAlgebraFunctor, comparison]
  simp only [bagMon.lift_eq_counit_app]

theorem aggregator_one : η ≫ aggregator M = η := by
  dsimp [aggregator, ofCommMon, lift]
  simp only [commMonToBagAlgebraFunctor, comparison]
  simp [IsMonHom.one_hom]

theorem aggregator_mul :
    μ ≫ aggregator M = (aggregator M ⊗ₘ aggregator M) ≫ μ := by
  dsimp [aggregator]
  simp only [IsMonHom.mul_hom]

theorem aggregator_singleton : singleton ≫ aggregator M = 𝟙 M.X := by
  dsimp [aggregator, ofCommMon, commMonToBagAlgebraFunctor]
  rw [← lift_eq_counit_app, singleton_lift]

theorem aggregator_join : join ≫ aggregator M = (map <| aggregator M) ≫ aggregator M := by
  dsimp [join, aggregator, ofCommMon]
  simp [commMonToBagAlgebraFunctor, comparison]
  simpa using (ofCommMon M).assoc

theorem aggregator_map {M' : CommMon C} {f : M.X ⟶ M'.X} :
    map f ≫ aggregator M' = aggregator M ≫ f := by
  sorry

theorem aggregator_ofList [ListArithmetic C] {M' : CommMon C} :
    ofList ≫ bag.aggregator M = M.toMon.aggregator := by
  sorry

end aggregator

end bag

end CategoryTheory
