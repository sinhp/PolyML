/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Monoidal.Category
import PolyML.ForMathlib.ConstantMorphism
-- import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

universe u v

namespace CategoryTheory

open Category Opposite Limits MonoidalCategory MorphismProperty

class SemiCartesianMonoidalCategory (C : Type u) [Category.{v} C] extends MonoidalCategory C where
  /-- The tensor unit is a terminal object. -/
  isTerminalTensorUnit : IsTerminal (𝟙_ C)

namespace SemiCartesianMonoidalCategory

variable {C : Type u} [Category.{v} C]

variable [SemiCartesianMonoidalCategory C]

/--
The unique map to the terminal object.
-/
def toUnit (X : C) : X ⟶ 𝟙_ C := isTerminalTensorUnit.from X

/-- The first projection from the tensor product. -/
def fst (X Y : C) : X ⊗ Y ⟶ X := (X ◁ toUnit Y) ≫ (ρ_ X).hom

/-- The second projection from the tensor product. -/
def snd (X Y : C) : X ⊗ Y ⟶ Y := (toUnit X ▷ Y) ≫ (λ_ Y).hom

def constMorphism (X : C) {Y : C} (y : 𝟙_ C ⟶ Y) : X ⟶ Y := MorphismProperty.constMorphism isTerminalTensorUnit X y

theorem const_self_eq_toUnit_self (X Y : C) (y : 𝟙_ C ⟶ Y) : constMorphism X y = toUnit X ≫ y := rfl

end SemiCartesianMonoidalCategory

end CategoryTheory

#min_imports
