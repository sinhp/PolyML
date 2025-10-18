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

class SemiCoCartesianMonoidalCategory (C : Type u) [Category.{v} C] extends MonoidalCategory C where
  /-- The tensor unit is a terminal object. -/
  isInitialTensorUnit : IsInitial (𝟙_ C)

namespace SemiCoCartesianMonoidalCategory

variable {C : Type u} [Category.{v} C]

variable [SemiCoCartesianMonoidalCategory C]

/--
The unique map to the terminal object.
-/
def fromUnit (X : C) : 𝟙_ C ⟶ X := isInitialTensorUnit.to X

/-- The first projection from the tensor product. -/
def inl (X Y : C) : X ⟶ X ⊗ Y := (ρ_ X).inv ≫ (X ◁ fromUnit Y)

/-- The second projection from the tensor product. -/
def inr (X Y : C) : Y ⟶ X ⊗ Y := (λ_ Y).inv ≫ (fromUnit X ▷ Y)

end SemiCoCartesianMonoidalCategory

end CategoryTheory

#min_imports
