/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import PolyML.ForMathlib.Monoidal.Semicartesian
import PolyML.ForMathlib.ConstantMorphism

universe u v

noncomputable section

namespace CategoryTheory

open Category Limits MonoidalCategory

variable {C : Type u} [Category.{v} C]

def bool (T : C) (_ : IsTerminal T := by aesop) [HasBinaryCoproducts C] := T ⨿ T

namespace bool

variable {T : C} (h : IsTerminal T) [HasBinaryCoproducts C]

def false : T ⟶ bool T := coprod.inl

def true : T ⟶ bool T := coprod.inr

def elim {X : C} (f : T ⟶ X) (g : T ⟶ X) : bool T ⟶ X := coprod.desc f g

end bool

namespace SemiCartesianMonoidalCategory

variable (C) [SemiCartesianMonoidalCategory C] [HasBinaryCoproducts C]

def bool := CategoryTheory.bool (𝟙_ C) (isTerminalTensorUnit)

variable {C}

def false : 𝟙_ C ⟶ bool C := bool.false (isTerminalTensorUnit)

def true : 𝟙_ C ⟶ bool C := bool.true (isTerminalTensorUnit)

def elim {X : C} (f : 𝟙_ C ⟶ X) (g : 𝟙_ C ⟶ X) : bool C ⟶ X := bool.elim (isTerminalTensorUnit) f g

def and : bool C ⊗ bool C ⟶ bool C := sorry

theorem false_and : (false ▷ (bool C)) ≫ and = constMorphism _ false := sorry

theorem true_and : (true ▷ (bool C)) ≫ and = (λ_ _).hom := sorry


end SemiCartesianMonoidalCategory

end CategoryTheory
