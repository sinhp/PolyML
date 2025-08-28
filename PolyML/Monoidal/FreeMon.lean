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

This provides a left adjoint to the forgetful functor from `Mon_ C` to `C`.

The development here is a categorification of `Mathlib.Algebra.FreeMonoid.Basic` for types.
-/


namespace CategoryTheory

open Category CategoryTheory ListArithmetic MonoidalCategory Mon_Class NNO Limits

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [ListArithmetic C]


/-- The free monoid functor given by the list objects of a list-arithmetic category. -/
@[simps]
def freeMon : C ⥤ Mon_ C where
  obj A := Mon_.mk (list A)
  map {X Y} f := Mon_.Hom.mk' (list.map f) (list.map_nil) (list.append_map)
  map_id := by aesop
  map_comp := by aesop

/-- Extends the isomorphism `listUnitIsoNNO` of the types to the monoids. -/
def freeMonUnitIsoMonNNO [BraidedCategory C] :
    (freeMon C).obj (𝟙_ C) ≅ Mon_.mk N := by
  refine Mon_.mkIso (listUnitIsoNNO C) ?_ ?_
  · simp [listUnitIsoNNO]
    aesop
  · simp [listUnitIsoNNO]
    sorry

namespace list

variable {C}

/-- Given a monoid object `M` in `C`, we define a morphism from `list X` to `M.X` by folding the list with the multiplication of the monoid. -/
def lift {X : C} {M : Mon_ C} (f : X ⟶ M.X) : list X ⟶ M.X :=
  list.foldr ((f ▷ M.X) ≫ μ[M.X]) η[M.X]

theorem lift_one {X : C} {M : Mon_ C} {f : X ⟶ M.X} :
    η ≫ list.lift f = η := by
  dsimp [lift, list.foldr, Mon_Class.one, list.nil]
  rw [plist.nil_rec]

theorem lift_mul {X : C} {M : Mon_ C} {f : X ⟶ M.X} :
    μ ≫ list.lift f = (list.lift f ⊗ₘ list.lift f) ≫ μ :=
  sorry

/-- The underlying functor of the list monad. -/
def functor : C ⥤ C := freeMon C ⋙ Mon_.forget C

theorem functor_obj (A : C) : functor.obj A = list A := by
  rfl

theorem functor_map {A B : C} (f : A ⟶ B) : functor.map f = list.map f := by
  rfl

/-- The adjoint transposition equivalence of the hom-sets. -/
def homEquiv (X : C) (M : Mon_ C) : ((freeMon C).obj X ⟶ M) ≃ (X ⟶ (Mon_.forget C).obj M) where
  toFun f := list.singleton ≫ f.hom
  invFun f := Mon_.Hom.mk' (list.lift f) list.lift_one list.lift_mul
  left_inv f := by
    refine Mon_.Hom.ext' ?_
    simp only [freeMon_obj_X]
    dsimp [lift,foldr]
    rw [← plist.rec_uniq]
    · dsimp [list]
      sorry
    · sorry
  right_inv f := sorry

variable (C)

/-- `list A` is a free monoid on the object `A` witnessed by the left adjoint of the forgetful functor from `Mon_ C` to `C`. -/
def freeMonForgetAdjunction : freeMon C ⊣ Mon_.forget C :=
  Adjunction.mkOfHomEquiv {
    homEquiv (X : C) (Y : Mon_ C) := homEquiv X Y
    homEquiv_naturality_left_symm := by
      intros X X' M g h
      simp only [Mon_.forget_obj]
      dsimp [homEquiv, Mon_.Hom.mk', freeMon, Mon_.Hom.mk']
      congr
      dsimp [list.lift]
      dsimp [list.foldr]
      rw [← plist.rec_uniq]
      · dsimp [list.map, plist.map]
        simp only [← assoc, plist.nil_rec]
      · dsimp [list.map, plist.map]
        rw [← assoc, plist.cons_rec, assoc, assoc, plist.cons_rec]
        simp only [whiskerLeft_comp, assoc]
        refine _ ≫= ?_
        rw [comp_whiskerRight, assoc, ← assoc, ← assoc _ (g ▷ M.X) (h ▷ M.X ≫ _)]
        refine ?_ =≫ _
        sorry
    homEquiv_naturality_right f g := by
      dsimp [homEquiv]; rw [assoc]}

section Monadicity

open Monad

instance hasReflexiveCoequalizersOfMon : HasReflexiveCoequalizers (Mon_ C) where
  has_coeq {A B} (f g) := sorry

instance preservesColimitOfIsReflexivePairOfMonForget :
    PreservesColimitOfIsReflexivePair (Mon_.forget C) where
  out {A B} (f g) r := sorry

instance monadicRightAdjointOfMonForget : MonadicRightAdjoint (Mon_.forget C) :=
  monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms <| freeMonForgetAdjunction C

end Monadicity

def monad : Monad C :=
  freeMonForgetAdjunction C |> Adjunction.toMonad

end list

def monToListAlgebraFunctor : Mon_ C ⥤ (list.monad C).Algebra := Monad.comparison _

/-- The equivalence between the category of algebras for the `list` monad and the category of monoids in `C`. -/
instance monToListAlgebraFunctorIsEquivalence [ListArithmetic C] : (monToListAlgebraFunctor C).IsEquivalence := by
  refine MonadicRightAdjoint.eqv

namespace list

variable {C}

def join {A : C} : list (list A) ⟶ list A := (monad C).μ.app A

theorem join_nil {A : C} : list.nil ≫ list.join = list.nil (C:=C) (A:=A)  := by
  dsimp [list.join, monad, freeMonForgetAdjunction, homEquiv, lift, list.foldr]
  simp [nil, plist.nil_rec]
  rfl

theorem flatten_nil {A : C} : list.nil ≫ list.flatten = list.nil (C:=C) (A:=A) := by
  dsimp [list.flatten]
  dsimp [list.rec]
  dsimp [list,list.nil]
  simp only [plist.nil_rec]

--flatten (xs:xss) = xs ++ flatten xss
theorem flatten_cons {A : C} :
  list.cons ≫ list.flatten = (list A ◁ list.flatten (A:=A)) ≫ list.append (A:=A) := by
  dsimp [list.flatten]
  dsimp [list.rec]
  dsimp [list.cons]
  rw [plist.cons_rec]

theorem join_cons {A : C} : list.cons ≫ list.join = list A ◁ list.join (A:=A) ≫ list.append := by
  sorry

theorem join_eq_flatten {A : C} : list.join (A := A) = list.flatten := by
  sorry

namespace Algebra

open Category

@[simps!]
def ofMon (M : Mon_ C) : (monad C).Algebra := monToListAlgebraFunctor _ |>.obj M

@[simp]
theorem ofMon_a_eq {M : Mon_ C} : (ofMon M).a = list.lift (𝟙 M.X) := by
  dsimp [ofMon, monToListAlgebraFunctor, Monad.comparison]
  rfl

instance monClass (α : (monad C).Algebra) : Mon_Class α.A where
  one := nil ≫ α.a
  mul := (singleton ⊗ₘ singleton) ≫ append ≫ α.a
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry

def mon (α : (monad C).Algebra) : Mon_ C where
  X := α.A

noncomputable def monToListAlgebraFunctorIsEquivalence' : (monad C).Algebra ≌ Mon_ C :=
  (monToListAlgebraFunctor C).asEquivalence.symm

-- SH: an explicit and constructive/computable construction of the equivalence without recourse to the monadicity theorem
def equivalenceMon : (monad C).Algebra ≌ Mon_ C where
  functor := {
    obj := mon
    map {α α'} f := Mon_.Hom.mk' f.1 (by sorry) (by sorry)
    map_id := sorry
    map_comp := sorry
  }
  inverse := monToListAlgebraFunctor C
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

end Algebra

end list

namespace Mon_

variable {C}

open list Algebra

def aggregator (M : Mon_ C) : list M.X ⟶ M.X := ofMon M |>.a

section aggregator

variable {M : Mon_ C}

theorem aggregator_one : η ≫ aggregator M = η := by
  exact lift_one

theorem aggregator_mul : μ ≫ aggregator M = (aggregator M ⊗ₘ aggregator M) ≫ μ := by
  exact lift_mul

theorem aggregator_singleton : list.singleton ≫ aggregator M = 𝟙 M.X := by
  dsimp [aggregator, ofMon, list.singleton]
  simp only [assoc]
  dsimp [lift, list.foldr, list.cons]
  sorry

theorem aggregator_join : list.join ≫ aggregator M = (map <| aggregator M) ≫ aggregator M := by
  sorry

/-- Theorem: Aggregator is functorial. -/
theorem aggregator_map {M' : Mon_ C} {f : M.X ⟶ M'.X} :
    map f ≫ aggregator M' = aggregator M ≫ f := by
  sorry

end aggregator

end Mon_

end CategoryTheory
