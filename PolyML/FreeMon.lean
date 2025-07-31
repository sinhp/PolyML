/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Algebra
import PolyML.ListArithmetic

/-
In this file, we prove that in a list-arithmetic category, the list object `list A` is a free monoid on the object `A`.
-/

namespace CategoryTheory

open Category CategoryTheory Recursive ListArithmetic Functor MonoidalCategory Mon_Class Monad

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
  dsimp [lift]
  dsimp [list.foldl]
  rw [← Category.assoc]
  dsimp [Mon_Class.one]
  dsimp [list.nil]
  rw [plist.rec_nil]

theorem lift_mul {X : C} {M : Mon_ C} {f : X ⟶ M.X} :
    μ ≫ list.lift f = (list.lift f ⊗ₘ list.lift f) ≫ μ := by
  dsimp [lift]
  rw [← lift_one (f := f)]
  dsimp [Mon_Class.mul]
  dsimp [list.foldl]
  have map_append {A B : C} {f : A ⟶ B} :
  list.append ≫ list.map f = ((list.map f) ⊗ₘ (list.map f)) ≫ list.append := list.map_append
  sorry

def functor : C ⥤ C := freeMon C ⋙ Mon_.forget C

theorem functor_obj (A : C) : functor.obj A = list A := rfl

theorem functor_map {A B : C} (f : A ⟶ B) : functor.map f = list.map f := rfl

/-- The adjoint transposition equivalence of the hom-sets. -/
def homEquiv (X : C) (M : Mon_ C) : ((freeMon C).obj X ⟶ M) ≃ (X ⟶ (Mon_.forget C).obj M) where
  toFun := fun f => list.singleton ≫ f.hom
  invFun := fun f => (Mon_.Hom.mk' (list.lift f) list.lift_one list.lift_mul)
  left_inv := by {
    sorry
  }
  right_inv := sorry

/-- `list A` is a free monoid on the object `A` witnessed by the left adjoint of the forgetful functor from `Mon_ C` to `C`. -/
def freeMonoidAdjunction : freeMon C ⊣ Mon_.forget C :=
  Adjunction.mkOfHomEquiv {
    homEquiv (X : C) (Y : Mon_ C) := homEquiv X Y
    homEquiv_naturality_left_symm f g := by { sorry}
    homEquiv_naturality_right := sorry
  }

def monad : Monad C :=
  freeMonoidAdjunction |> Adjunction.toMonad

def join {A : C} : list (list A) ⟶ list A := monad.μ.app A

/--
Haskell equivalent:

join :: Monad m => m (m a) -> m a
join = flatten

This theorem states that `list.join` is equal to `list.flatten`, similar to how Haskell's `join` function for monads is equivalent to `flatten`.
-/
theorem join_eq_flatten {A : C} : list.join (A := A) = list.flatten := by {
  dsimp [list.join]
  dsimp [list.flatten]
  dsimp [list.rec']
  sorry
}

namespace algebra

/-- A monoid structure on `A` gives rise to an algebra for the `list` monad. -/
def ofMon (M : Mon_ C) : Algebra (list.monad (C:= C)) where
  A := M.X
  a := lift (𝟙 _)
  unit := sorry
  assoc := sorry

end algebra

open algebra

def aggregator (M : Mon_ C) : list M.X ⟶ M.X :=
  (ofMon M).a

theorem aggregator_one {M : Mon_ C} :
  η ≫ aggregator M = η := lift_one

theorem aggregator_mul {M : Mon_ C} :
  μ ≫ aggregator M = (aggregator M ⊗ₘ aggregator M) ≫ μ := lift_mul

theorem aggregator_singleton {M : Mon_ C} :
  list.singleton ≫ aggregator M = 𝟙 M.X := by
  dsimp [aggregator]
  dsimp [ofMon]
  dsimp [list.singleton]
  simp only [Category.assoc]
  dsimp [lift]
  dsimp [list.foldl]
  dsimp [list.cons]
  rw [plist.rec_cons]
  simp only [MonoidalCategory.whiskerLeft_id, id_comp,
    BraidedCategory.braiding_naturality_right_assoc]
  sorry

theorem aggregator_join {M : Mon_ C} :
  list.join ≫ aggregator M = (list.map <| aggregator M) ≫ aggregator M := by
  rw [CategoryTheory.list.join_eq_flatten]
  dsimp [list.flatten]
  dsimp [list.rec']
  sorry

/-- Theorem: Aggregator is functorial. -/
theorem aggregator_map {M : Mon_ C} {f : M.X ⟶ M'.X} :
  list.map f ≫ aggregator M' = aggregator M ≫ f := by
  sorry

end list

end CategoryTheory
