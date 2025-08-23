/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import PolyML.ForMathlib.Monoidal.SemiCartesian
import PolyML.ForMathlib.ConstantMorphism

universe u v

noncomputable section

namespace CategoryTheory

open Category Limits MonoidalCategory

variable {C : Type u} [Category.{v} C]

def boolOf (T : C) (_ : IsTerminal T := by aesop) [HasBinaryCoproducts C] := T ⨿ T

namespace boolOf

variable {T : C} (h : IsTerminal T) [HasBinaryCoproducts C]

def false : T ⟶ boolOf T := coprod.inl

def true : T ⟶ boolOf T := coprod.inr

def elim {X : C} (f : T ⟶ X) (g : T ⟶ X) : boolOf T ⟶ X := coprod.desc f g

end boolOf

namespace SemiCartesianMonoidalCategory

variable [SemiCartesianMonoidalCategory C] [HasBinaryCoproducts C]

def bool := CategoryTheory.boolOf (𝟙_ C) (isTerminalTensorUnit)

namespace bool

scoped notation "𝟮" => bool

def false : 𝟙_ C ⟶ 𝟮 := boolOf.false (isTerminalTensorUnit)

def true : 𝟙_ C ⟶ 𝟮 := boolOf.true (isTerminalTensorUnit)

def elim {X : C} (f : 𝟙_ C ⟶ X) (g : 𝟙_ C ⟶ X) : 𝟮 ⟶ X := boolOf.elim (isTerminalTensorUnit) f g

def and : (𝟮 : C) ⊗ 𝟮 ⟶ 𝟮 := sorry

theorem false_and : (false ▷ (𝟮 : C)) ≫ and = constMorphism _ false := sorry

theorem true_and : (true ▷ (𝟮 : C)) ≫ and = (λ_ _).hom := sorry

end bool

end SemiCartesianMonoidalCategory

end CategoryTheory
