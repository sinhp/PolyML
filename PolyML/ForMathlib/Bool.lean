/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import PolyML.ForMathlib.ConstantMorphism
import Mathlib.CategoryTheory.Distributive.Monoidal

universe u v

noncomputable section

namespace CategoryTheory

open Limits

-- section

-- variable {C : Type u} [Category.{v} C]

-- def boolOf (T : C) (_ : IsTerminal T := by aesop) [HasBinaryCoproducts C] := T ⨿ T

-- variable {T : C} (h : IsTerminal T) [HasBinaryCoproducts C]

-- private def false : T ⟶ boolOf T := coprod.inl

-- private def true : T ⟶ boolOf T := coprod.inr

-- private def elim {X : C} (f : T ⟶ X) (g : T ⟶ X) : boolOf T ⟶ X := coprod.desc f g

-- end

namespace MonoidalCategory

open Category Limits

class IsBool {C : Type u} [Category.{v} C] [MonoidalCategory C] (obj : C) (ff tt : 𝟙_ C ⟶ obj) where
  elim {ff} {tt} {X : C} (a : 𝟙_ C ⟶ X) (b : 𝟙_ C ⟶ X) : obj ⟶ X
  ff_elim {X : C} {a : 𝟙_ C ⟶ X} {b : 𝟙_ C ⟶ X} :
    ff ≫ elim a b = a
  tt_elim {X : C} {a : 𝟙_ C ⟶ X} {b : 𝟙_ C ⟶ X} :
    tt ≫ elim a b = b
  elim_uniq {X : C} {a : 𝟙_ C ⟶ X} {b : 𝟙_ C ⟶ X} (f : obj ⟶ X)
    (h0 : ff ≫ f = a) (h1 : tt ≫ f = b) : f = elim a b

attribute [reassoc (attr := simp)] IsBool.ff_elim IsBool.tt_elim

class Bool (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  /-- The object of booleans. -/
  obj (C) : C
  ff : 𝟙_ C ⟶ obj
  tt : 𝟙_ C ⟶ obj
  [isBool : IsBool obj ff tt]

attribute [instance] Bool.isBool

scoped notation "𝟮_ " => Bool.obj

namespace Bool

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

open IsBool

variable [Bool C]

abbrev elim {X : C} (f : 𝟙_ C ⟶ X) (g : 𝟙_ C ⟶ X) : 𝟮_ C ⟶ X :=
  IsBool.elim (ff := Bool.ff) (tt := Bool.tt)  f g

lemma eta {X : C} (f : 𝟮_ C ⟶ X) : Bool.elim (Bool.ff ≫ f) (Bool.tt ≫ f) = f := by
  sorry

@[simp]
lemma elim_eta_left {X : C} (f : 𝟮_ C ⟶ X) :
    Bool.ff ≫ Bool.elim (Bool.ff ≫ f) (Bool.tt ≫ f) = Bool.ff ≫ f := by
  simp only [eta]

@[simp]
lemma elim_eta_right {X : C} (f : 𝟮_ C ⟶ X) :
    Bool.tt ≫ Bool.elim (Bool.ff ≫ f) (Bool.tt ≫ f) = Bool.tt ≫ f := by
  simp only [eta]

@[ext]
lemma hom_ext {X : C} {f g : 𝟮_ C ⟶ X}
    (h0 : Bool.ff ≫ f = Bool.ff ≫ g) (h1 : Bool.tt ≫ f = Bool.tt ≫ g) : f = g := by
  rw [← eta f]
  rw [← eta g]
  grind

/-- Two presentations with identical branch values are equal. -/
lemma elim_congr {X : C} {a a' b b' : 𝟙_ C ⟶ X}
    (h0 : a = a') (h1 : b = b') : elim a b = elim a' b' := by
  subst h0 h1
  rfl

@[simp]
lemma elim_comp {X : C} {a b : 𝟙_ C ⟶ X} {Y : C} (k : X ⟶ Y) :
    elim a b ≫ k = elim (a ≫ k) (b ≫ k) := by
  apply hom_ext
  simp [elim]
  sorry

lemma elim_iff {X : C} {f : 𝟮_ C ⟶ X} {a b : 𝟙_ C ⟶ X} :
    elim a b = f ↔ (Bool.ff ≫ f = a ∧ Bool.tt ≫ f = b) := by
  constructor
  · intro h; subst h; simp
  · intro h; rcases h with ⟨h0, h1⟩
    apply hom_ext
    · rw [IsBool.ff_elim]
      exact h0.symm
    · rw [IsBool.tt_elim]
      exact h1.symm

def constTrue : 𝟮_ C ⟶ 𝟮_ C := elim tt tt

def constFalse : 𝟮_ C ⟶ 𝟮_ C := elim ff ff

def toUnit : 𝟮_ C ⟶ 𝟙_ C := elim (𝟙 _) (𝟙 _)

theorem constTrue_toUnit : constTrue ≫ toUnit (C:= C) = toUnit := by
  simp only [constTrue, elim_comp, toUnit]
  congr 1
  all_goals
  simp only [IsBool.tt_elim]

theorem constTrue_eq_toUnit_true : constTrue (C:= C) = toUnit ≫ tt := by
  dsimp only [constTrue, toUnit, false, true]
  apply elim_iff.mpr
  simp

def not : 𝟮_ C ⟶ 𝟮_ C := elim tt ff

end Bool

open Bool

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasBinaryCoproducts C]

/-- A monoidal caetegory with binary coproducts has booleans. -/
@[simps]
def boolOfBinaryCoproduct : Bool C where
  obj := (𝟙_ C) ⨿ (𝟙_ C)
  ff := coprod.inl
  tt := coprod.inr
  isBool := {
    elim := fun {X} a b => coprod.desc a b
    ff_elim := by simp [coprod.inl, coprod.desc]
    tt_elim := by simp [coprod.inr, coprod.desc]
    elim_uniq := by
      intro X a b f h0 h1
      apply coprod.hom_ext
      · rw [coprod.inl_desc]; exact h0
      · rw [coprod.inr_desc]; exact h1 }

attribute [local instance] boolOfBinaryCoproduct

-- break 𝟮_ C into the sum 𝟙_ C and 𝟙_ C and use distrib.
def and [HasBinaryCoproducts C] [IsMonoidalLeftDistrib C] : 𝟮_ C ⊗ 𝟮_ C ⟶ 𝟮_ C := sorry

theorem false_and [HasBinaryCoproducts C] [IsMonoidalLeftDistrib C] :
    (ff ▷ (𝟮_ C)) ≫ and = (λ_ _).hom ≫ (elim (C:= C) (X:= 𝟮_ C) tt tt) := by
  sorry

-- theorem false_and' [SemiCartesianMonoidalCategory C] :
--     (false ▷ (𝟮 : C)) ≫ and = SemiCartesianMonoidalCategory.constMorphism _ false := sorry

theorem true_and [HasBinaryCoproducts C] [IsMonoidalLeftDistrib C] : (tt ▷ 𝟮_ C) ≫ and = (λ_ _).hom := sorry



end MonoidalCategory

end CategoryTheory
