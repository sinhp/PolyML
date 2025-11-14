/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.MorphismProperty.Composition

universe u v

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

def IsConstant : MorphismProperty C := fun {X Y} (f : X ⟶ Y) => ∀ {Z} (g h : Z ⟶ X), g ≫ f = h ≫ f
section ConstantMorphism

variable (T : C) (h : IsTerminal T := by infer_instance)

def constMorphismFrom (X : C) {Y : C} (y : T ⟶ Y) : X ⟶ Y := h.from X ≫ y

variable {X Y : C}

variable {T}

/-- A morphism `f : X ⟶ Y` is constant at `y : T ⟶ Y` if it factors through the terminal object via `y`. -/
def ConstantAt (f : X ⟶ Y) (y : T ⟶ Y) : Prop := f = h.from X ≫ y

theorem constant_isConstantAt (y : T ⟶ Y) :
    ConstantAt h (constMorphismFrom T h X y) y := by
  rfl

theorem eq_constant_isConstantAt {f : X ⟶ Y} {y : T ⟶ Y} :
    ConstantAt h f y ↔ f = constMorphismFrom T h X y := by
  rfl

/-- The precomposition of a constant morphism with any morphism remains constant. -/
theorem isConstantAt_precompose {f : X ⟶ Y} {y : T ⟶ Y} (h_const : ConstantAt h f y) {X' : C} (g : X' ⟶ X) :
    ConstantAt (h:= h) (g ≫ f) y := by
  unfold ConstantAt
  rw [h_const]
  simp [← assoc, IsTerminal.comp_from]

theorem const_precompose {Z} {f : X ⟶ Y} {z : T ⟶ Z} :
  f ≫ constMorphismFrom T h Y z = constMorphismFrom T h X z := by
  rw [← eq_constant_isConstantAt h]
  apply isConstantAt_precompose
  apply constant_isConstantAt

def Constant : MorphismProperty C := fun {X Y} (f : X ⟶ Y) => ∃ y : T ⟶ Y, ConstantAt (h:= h) f y

theorem isConstantAt_isConstant (f : X ⟶ Y) (y : T ⟶ Y) :
    ConstantAt h f y → Constant h f := by
  intro h_const
  use y

/-- Constant morphisms compose with any morphism to remain constant -/
theorem isConstantAt_postcompose {f : X ⟶ Y} {y : T ⟶ Y} (h_const : ConstantAt (h:= h) f y)
    {Z : C} (k : Y ⟶ Z) : ConstantAt h (f ≫ k) (y ≫ k) := by
  unfold ConstantAt
  rw [h_const, assoc]

/-- Postcomposition preserves the constant property -/
theorem constant_postcompose {f : X ⟶ Y} (h_const : Constant h f) {Z : C} (k : Y ⟶ Z) :
    Constant h (f ≫ k) := by
  obtain ⟨y, hy⟩ := h_const
  exact ⟨y ≫ k, isConstantAt_postcompose h hy k⟩

instance : IsStableUnderComposition (C:= C) (Constant h) where
   comp_mem {X Y Z} f g cf cg := by
    apply constant_postcompose
    all_goals
    assumption

/-- The postcomposition of a constant morphism with any morphism gives a constant morphism. -/
theorem const_postcompose {Z} {z : T ⟶ Y} {g : Y ⟶ Z} :
  constMorphismFrom T h X z ≫ g = constMorphismFrom T h X (z ≫ g) := by
  rw [← eq_constant_isConstantAt h]
  apply isConstantAt_postcompose
  apply constant_isConstantAt

/-- The identity morphism from the terminal object is constant -/
theorem terminal_id_isConstant : Constant h (𝟙 T) := by
  use 𝟙 T
  unfold ConstantAt
  rw [← comp_id (h.from T)]
  exact IsTerminal.hom_ext h _ _

/-- Any morphism from the terminal object is constant -/
theorem from_terminal_isConstant (y : T ⟶ Y) : Constant h y := by
  use y
  unfold ConstantAt
  have : h.from T = 𝟙 T := IsTerminal.hom_ext h _ _
  rw [this, id_comp]

end ConstantMorphism

end MorphismProperty

end CategoryTheory
