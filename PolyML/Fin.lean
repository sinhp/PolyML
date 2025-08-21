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
import PolyML.NNO


import Mathlib

/-
In this file, we prove that in a list-arithmetic category, the list object `list A` is a free monoid on the object `A`.
Our development here is a categorification of `Mathlib.Algebra.FreeMonoid.Basic` for types.
-/
namespace CategoryTheory

open Category CategoryTheory Recursive NNO Functor MonoidalCategory Mon_Class Monad Limits

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [NNO C] [HasPullbacks C]

attribute [local instance] CartesianMonoidalCategory.toSymmetricCategory
attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

#check CartesianMonoidalCategory.ofChosenFiniteProducts

#check ChosenFiniteProducts

#check FinEnum

#check CategoryTheory.Limits.isInitialOfIsPullbackOfCoproduct

noncomputable def fin (n : 𝟙_ C ⟶ N) := pullback n (add ≫ succ)

noncomputable def isInitialFinZero : IsInitial (fin zero : C) := by
  -- fin zero is the pullback of zero : 𝟙_ C ⟶ N and add ≫ succ : N ⟶ N
  -- Since zero is initial in NNO, the pullback is initial
  letI : (Y : C) → Unique (fin zero ⟶ Y) := by {
    intros Y
    sorry
  }
  exact IsInitial.ofUnique (C:=C) (X:=fin zero)

noncomputable def finZeroIso [HasInitial C] : fin zero ≅ ⊥_ C :=
  (initialIsoIsInitial isInitialFinZero).symm

def finSuccIso [ HasBinaryCoproducts C] (n : 𝟙_ C ⟶ N) : fin (n ≫ succ) ≅ 𝟙_ C ⨿ fin n where
  hom := sorry
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

noncomputable def isTerminalFinOne : IsTerminal (fin NNO.one : C) := by {
  refine IsZero.isTerminal ?_
  constructor
  · intros Y
    refine IsZero.unique_to ?_ Y
    sorry
  · sorry
}

#check ConcreteCategory

/-- For an object `X : C`, the structure `FinEnum X` consists of a natural number `n` and an
isomorphism `X ≅ nno.fin n`. This means that `X` is finite and can be enumerated in some order. -/
class FinEnum (X : C) where
  card : 𝟙_ C ⟶ N
  iso : X ≅ fin card
