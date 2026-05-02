/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monad.Monadicity
import PolyML.Monoidal.NNO
import PolyML.Monoidal.ListArithmetic


/-!
# Free Monoid Monad

In this file, we prove that in a list-arithmetic category, the list object `list A` is a free monoid on the object `A`.

This provides a left adjoint to the forgetful functor from `Mon C` to `C`.

The development here is a categorification of `Mathlib.Algebra.FreeMonoid.Basic` for types.
-/


namespace CategoryTheory

open Category CategoryTheory ListArithmetic MonoidalCategory MonObj PNNO Limits

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [ListArithmetic C]


/-- The free monoid functor given by the list objects of a list-arithmetic category. -/
@[simps]
def freeMon : C ⥤ Mon C where
  obj A := Mon.mk (list A)
  map {X Y} f := Mon.Hom.mk' (list.map f) (list.map_nil) (list.append_map)
  map_id := by aesop
  map_comp := by aesop

attribute [local instance] AddMonObj.toMonObj
-- attribute [local instance] AddMon.toMon

/-- Extends the isomorphism `listUnitIsoNNO` of the types to the monoids. -/
def freeMonUnitIsoMonNNO [BraidedCategory C] :
    (freeMon C).obj (𝟙_ C) ≅ Mon.mk N := by
  refine Mon.mkIso (listUnitIsoNNO C) ?_ ?_
  · simp [listUnitIsoNNO]
    aesop
  · simp [listUnitIsoNNO]
    dsimp [MonObj.mul, add, iter, prc]
    apply list.prc_uniq
    · aesop --simp only [list.whiskerRight_nil_append, comp_id]
    · simp [list.append]
      rw [← Category.assoc, list.cons_prc]
      simp only [id_whiskerLeft, Category.assoc]

namespace list

variable {C}

/-- Given a monoid object `M` in `C`, we define a morphism from `list X` to `M.X` by folding the list with the multiplication of the monoid. -/
def lift {X : C} {M : Mon C} (f : X ⟶ M.X) : list X ⟶ M.X :=
  list.foldr ((f ▷ M.X) ≫ μ[M.X]) η[M.X]

theorem lift_one {X : C} {M : Mon C} {f : X ⟶ M.X} :
    η ≫ list.lift f = η := by
  dsimp [lift, list.foldr, MonObj.one, list.nil]
  rw [plist.nil_rc]

theorem lift_one_whiskerRight {M : Mon C} {f : X ⟶ M.X} {Y : C} :
  (η ▷ X) ≫ (list.lift f ▷ X) = η ▷ X := by
  dsimp [lift, list.foldr, MonObj.one, list.nil]
  apply plist.whiskerRight_nil_whiskerRight_rc

theorem lift_mul {X : C} {M : Mon C} {f : X ⟶ M.X} :
    μ ≫ list.lift f = (list.lift f ⊗ₘ list.lift f) ≫ μ := by
  sorry

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
  left_inv f := by sorry
  right_inv f := by sorry

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

instance hasReflexiveCoequalizersOfMon : HasReflexiveCoequalizers (Mon C) where
  has_coeq {A B} (f g) := sorry

instance preservesColimitOfIsReflexivePairOfMonForget :
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
