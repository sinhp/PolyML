/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monoidal.Mon_
import PolyML.ListArithmetic

/-
In this file, we prove that in a list-arithmetic category, the list object `list A` is a free monoid on the object `A`.
-/


namespace CategoryTheory

open ListArithmetic

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
[Recursive C] [ListArithmetic C]

-- from here we are trying to prove that list is the free monoid object in a list-arithmetic category.
def lift {A : C} {M : Mon_ C} (f : A ⟶ M.X) : list A ⟶ M.X :=
  sorry


end CategoryTheory
