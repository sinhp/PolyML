/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import PolyML.ListArithmetic

/-
In this file, we prove that in a list-arithmetic category, the list object `list A` is a free monoid on the object `A`.
-/

namespace CategoryTheory

open Category CategoryTheory Recursive ListArithmetic Functor MonoidalCategory Mon_Class

universe v u

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] [ListArithmetic C]

/-- The free monoid functor given by the list objects of a list-arithmetic category. -/
@[simps]
def freeMon : C ⥤ Mon_ C where
  obj A := Mon_.mk (list A)
  map {X Y} f := Mon_.Hom.mk' (list.map f) (list.map_nil) (list.map_append)
  map_id := by aesop
  map_comp := by aesop

namespace list

variable {C}

/-- Given a monoid object `M` in `C`, we define a morphism from `list X` to `M.X` by folding the list with the multiplication of the monoid. -/
def lift {X : C} {M : Mon_ C} (f : X ⟶ M.X) : list X ⟶ M.X :=
  list.foldl ((M.X ◁ f) ≫ μ[M.X]) η[M.X]

theorem lift_one {X : C} {M : Mon_ C} {f : X ⟶ M.X} :
    η ≫ list.lift f = η := by
  sorry

theorem lift_mul {X : C} {M : Mon_ C} {f : X ⟶ M.X} :
    μ ≫ list.lift f = (list.lift f ⊗ₘ list.lift f) ≫ μ := by
  sorry

def functor : C ⥤ C := freeMon C ⋙ Mon_.forget C

theorem functor_obj (A : C) : functor.obj A = list A := rfl

theorem functor_map {A B : C} (f : A ⟶ B) : functor.map f = list.map f := rfl

end list

variable {C}

/-- The adjoint transposition equivalence of the hom-sets. -/
def homEquiv (X : C) (M : Mon_ C) : ((freeMon C).obj X ⟶ M) ≃ (X ⟶ (Mon_.forget C).obj M) where
  toFun := fun f => list.singleton ≫ f.hom
  invFun := fun f => (Mon_.Hom.mk' (list.lift f) list.lift_one list.lift_mul)
  left_inv := sorry
  right_inv := sorry

/-- `list A` is a free monoid on the object `A` witnessed by the left adjoint of the forgetful functor from `Mon_ C` to `C`. -/
def freeMonoidAdjunction : freeMon C ⊣ Mon_.forget C :=
  Adjunction.mkOfHomEquiv {
    homEquiv (X : C) (Y : Mon_ C) := homEquiv X Y
    homEquiv_naturality_left_symm := sorry
    homEquiv_naturality_right := sorry
  }

end CategoryTheory
