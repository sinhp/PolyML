/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Monoidal.Category

universe u v

namespace CategoryTheory

open Category Opposite Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace MonoidalCategory

def toUnit (h : IsTerminal (𝟙_ C)) (A : C) : A ⟶ 𝟙_ C := h.from _

end MonoidalCategory

namespace ConstantMorphism

variable (h : IsTerminal (𝟙_ C))

def const (X : C) {Y : C} (y : 𝟙_ C ⟶ Y) : X ⟶ Y := toUnit h X ≫ y

variable {X Y : C}

/-- A morphism `f : X ⟶ Y` is constant at `y : 𝟙_ C ⟶ Y` if it factors through the terminal object via `y`. -/
def IsConstantAt (f : X ⟶ Y) (y : 𝟙_ C ⟶ Y) : Prop := f = toUnit h X ≫ y

theorem constant_isConstantAt (y : 𝟙_ C ⟶ Y) :
    IsConstantAt h (const h X y) y := by
  rfl

theorem eq_constant_isConstantAt {f : X ⟶ Y} {y : 𝟙_ C ⟶ Y} :
    IsConstantAt h f y ↔ f = const h X y := by
  rfl

/-- The precomposition of a constant morphism with any morphism remains constant. -/
theorem isConstantAt_precompose {f : X ⟶ Y} {y : 𝟙_ C ⟶ Y} (h_const : IsConstantAt h f y) {X' : C} (g : X' ⟶ X) :
    IsConstantAt (h:= h) (g ≫ f) y := by
  unfold IsConstantAt
  rw [h_const]
  simp [← assoc, toUnit, IsTerminal.comp_from]

theorem const_precompose {Z} {f : X ⟶ Y} {z : 𝟙_ C ⟶ Z} :
  f ≫ const h Y z = const h X z := by
  rw [← eq_constant_isConstantAt]
  apply isConstantAt_precompose
  apply constant_isConstantAt

def IsConstant (f : X ⟶ Y) : Prop := ∃ y : 𝟙_ C ⟶ Y, IsConstantAt (h:= h) f y

theorem isConstantAt_isConstant (f : X ⟶ Y) (y : 𝟙_ C ⟶ Y) :
    IsConstantAt h f y → IsConstant h f := by
  intro h_const
  use y

/-- Constant morphisms compose with any morphism to remain constant -/
theorem isConstantAt_postcompose {f : X ⟶ Y} {y : 𝟙_ C ⟶ Y} (h_const : IsConstantAt (h:= h) f y)
    {Z : C} (k : Y ⟶ Z) : IsConstantAt h (f ≫ k) (y ≫ k) := by
  unfold IsConstantAt
  rw [h_const, assoc]

/-- Postcomposition preserves the constant property -/
theorem isConstant_postcompose {f : X ⟶ Y} (h_const : IsConstant (h:= h) f) {Z : C} (k : Y ⟶ Z) :
    IsConstant (h:= h) (f ≫ k) := by
  obtain ⟨y, hy⟩ := h_const
  exact ⟨y ≫ k, isConstantAt_postcompose h hy k⟩

/-- The postcomposition of a constant morphism with any morphism gives a constant morphism. -/
theorem const_postcompose {Z} {z : 𝟙_ C ⟶ Y} {g : Y ⟶ Z} :
  const h X z ≫ g = const h X (z ≫ g) := by
  rw [← eq_constant_isConstantAt]
  apply isConstantAt_postcompose
  apply constant_isConstantAt

/-- The identity morphism from the terminal object is constant -/
theorem terminal_id_isConstant : IsConstant (h:= h) (𝟙 (𝟙_ C)) := by
  use 𝟙 (𝟙_ C)
  unfold IsConstantAt toUnit
  rw [← comp_id (h.from (𝟙_ C))]
  exact IsTerminal.hom_ext h _ _

/-- Any morphism from the terminal object is constant -/
theorem from_terminal_isConstant (y : 𝟙_ C ⟶ Y) : IsConstant (h:= h) y := by
  use y
  unfold IsConstantAt toUnit
  have : h.from (𝟙_ C) = 𝟙 (𝟙_ C) := IsTerminal.hom_ext h _ _
  rw [this, id_comp]

end ConstantMorphism

end CategoryTheory
