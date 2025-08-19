/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Category.Factorisation
import PolyML.ListArithmetic

universe u v

namespace CategoryTheory

open Category Opposite Limits MonoidalCategory CartesianMonoidalCategory

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

open Endofunctor Algebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {h : IsTerminal (𝟙_ C)} {X Y : C}

def toUnit (h : IsTerminal (𝟙_ C)) (A : C) : A ⟶ 𝟙_ C := h.from _

def constantAt (f : X ⟶ Y) (y : 𝟙_ C ⟶ Y) : Prop :=  f = toUnit h X ≫ y

def constantAt_precompose {f : X ⟶ Y} {y : 𝟙_ C ⟶ Y} (h_const : constantAt (h:= h) f y) {X' : C} {g : X' ⟶ X} :
    constantAt (h:= h) (g ≫ f) y := by
  unfold constantAt
  rw [h_const]
  simp [← assoc, toUnit, IsTerminal.comp_from]

def constant (f : X ⟶ Y) : Prop := ∃ y : 𝟙_ C ⟶ Y, constantAt (h:= h) f y

/-- Precomposition preserves the constant property -/
theorem constant_precompose {f : X ⟶ Y} (h_const : constant (h:= h) f) {X' : C} (g : X' ⟶ X) :
    constant (h:= h) (g ≫ f) := by
  obtain ⟨y, hy⟩ := h_const
  exact ⟨y, constantAt_precompose hy⟩

/-- A morphism is constant at y iff it factors through the terminal object via y -/
theorem constantAt_iff_factors (f : X ⟶ Y) (y : 𝟙_ C ⟶ Y) :
    constantAt (h:= h) f y ↔ f = toUnit h X ≫ y := by
  rfl

/-- Constant morphisms compose with any morphism to remain constant -/
theorem constantAt_postcompose {f : X ⟶ Y} {y : 𝟙_ C ⟶ Y} (h_const : constantAt (h:= h) f y)
    {Z : C} (k : Y ⟶ Z) : constantAt (h:= h) (f ≫ k) (y ≫ k) := by
  unfold constantAt
  rw [h_const, assoc]

/-- Postcomposition preserves the constant property -/
theorem constant_postcompose {f : X ⟶ Y} (h_const : constant (h:= h) f) {Z : C} (k : Y ⟶ Z) :
    constant (h:= h) (f ≫ k) := by
  obtain ⟨y, hy⟩ := h_const
  exact ⟨y ≫ k, constantAt_postcompose hy k⟩

/-- The identity morphism from the terminal object is constant -/
theorem terminal_id_constant : constant (h:= h) (𝟙 (𝟙_ C)) := by
  use 𝟙 (𝟙_ C)
  unfold constantAt toUnit
  rw [← comp_id (h.from (𝟙_ C))]
  exact IsTerminal.hom_ext h _ _

/-- Any morphism from the terminal object is constant -/
theorem from_terminal_constant (y : 𝟙_ C ⟶ Y) : constant (h:= h) y := by
  use y
  unfold constantAt toUnit
  -- Since h.from (𝟙_ C) : 𝟙_ C ⟶ 𝟙_ C and y : 𝟙_ C ⟶ Y
  -- We need to show y = h.from (𝟙_ C) ≫ y
  -- Since (𝟙_ C) is terminal, h.from (𝟙_ C) is the identity
  have : h.from (𝟙_ C) = 𝟙 (𝟙_ C) := IsTerminal.hom_ext h _ _
  rw [this, id_comp]

end CategoryTheory
