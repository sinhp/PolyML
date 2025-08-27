/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import PolyML.ForMathlib.Monad.Distrib
import PolyML.ForMathlib.Monoidal.AddMon_
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Distributive.Monoidal


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory Comon_Class Monad

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]

def s23 {X Y Z W : C} : (X ⊗ Y) ⊗ (Z ⊗ W) ⟶ (X ⊗ Z) ⊗ (Y ⊗ W) := by
  exact tensorμ X Y Z W

class Distrib (X : C) [Comon_Class X] extends Mon_Class X, AddMon_Class X where
  left_distrib : Δ ▷ (X ⊗ X) ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ mul = X ◁ add ≫ mul
  right_distrib : (X ⊗ X) ◁ Δ ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ mul = add ▷ X ≫ mul

class LeftDistrib (X : C) [Comon_Class X] extends Mon_Class X, AddMon_Class X where
  left_distrib : Δ ▷ (X ⊗ X) ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ mul = X ◁ add ≫ mul

class RightDistrib (X : C) [Comon_Class X] extends Mon_Class X, AddMon_Class X where
  right_distrib : (X ⊗ X) ◁ Δ ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ mul = add ▷ X ≫ mul

instance (priority := 100) Distrib.leftDistribClass (X : C) [Comon_Class X] [Distrib X] : LeftDistrib X :=
  ⟨Distrib.left_distrib⟩

alias mul_add := left_distrib

instance (priority := 100) Distrib.rightDistribClass (X : C) [Comon_Class X] [Distrib X] : RightDistrib X :=
  ⟨Distrib.right_distrib⟩

alias add_mul := right_distrib

#exit

def Semiring_ := LiftingMonad.monad (list.monad C) (bag.monad C) |>.Algebra

end CategoryTheory

open Distrib Monad



namespace Semiring_

variable {C} (α : Semiring_ C)

def X : C := α.A.A

instance mon_Class : Mon_Class α.X where
  one := by
    dsimp [X]
    dsimp [Semiring_] at α
    sorry
  mul := by
    dsimp [X];
    sorry
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry

def mon : Mon_ C where
  X := α.X

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

instance commMon : CommMon_ C where
  X := α.X
  mon := sorry
  comm := sorry

end Semiring_

end CategoryTheory
