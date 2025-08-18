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


import Mathlib

/-
In this file, we prove that in a list-arithmetic category, the list object `list A` is a free monoid on the object `A`.
Our development here is a categorification of `Mathlib.Algebra.FreeMonoid.Basic` for types.
-/
namespace CategoryTheory

open Category CategoryTheory Recursive ListArithmetic Functor MonoidalCategory Mon_Class Monad Limits

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [ListArithmetic C] [HasFiniteLimits C]

attribute [local instance] CartesianMonoidalCategory.toSymmetricCategory
attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

#check CartesianMonoidalCategory.ofChosenFiniteProducts

#check ChosenFiniteProducts

#check FinEnum

namespace nno

noncomputable def fin (n : 𝟙_ C ⟶ N_ C) := pullback n (add ≫ succ)

def isInitialFinZero : IsInitial (fin zero : C) := by sorry

def finZeroIso [HasInitial C] : fin zero ≅ ⊥_ C := sorry

def finSuccIso [ HasBinaryCoproducts C] (n : 𝟙_ C ⟶ N_ C) : fin (n ≫ nno.succ) ≅ 𝟙_ C ⨿ fin n := by
  sorry

def isTerminalFinOne : IsTerminal (fin one : C) := by sorry

end nno
