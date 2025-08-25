/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import PolyML.ForMathlib.Monoidal.SemiCartesian
import PolyML.ForMathlib.ConstantMorphism
import Mathlib.CategoryTheory.Distributive.Monoidal

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

namespace MonoidalCategory

variable [MonoidalCategory C] [HasBinaryCoproducts C]

def bool := (𝟙_ C) ⨿ (𝟙_ C)

namespace bool

open coprod

scoped notation "𝟮" => bool

def false : 𝟙_ C ⟶ 𝟮 := inl

def true : 𝟙_ C ⟶ 𝟮 := inr

def elim {X : C} (f : 𝟙_ C ⟶ X) (g : 𝟙_ C ⟶ X) : 𝟮 ⟶ X := desc f g

@[simp]
lemma false_elim {X : C} (f0 f1 : 𝟙_ C ⟶ X) : false ≫ elim f0 f1 = f0 := by
  dsimp [mk, bool.false, false, elim]
  simp

@[simp]
lemma true_elim {X : C} {f0 f1 : 𝟙_ C ⟶ X} : true ≫ bool.elim f0 f1 = f1 := by
  dsimp [elim, bool.true, true]
  simp

lemma ext {X : C} {f g : 𝟮 ⟶ X}
    (h0 : false ≫ f = false ≫ g) (h1 : true ≫ f = true ≫ g) : f = g := by
  apply coprod.hom_ext
  · simpa [bool.false, false] using h0
  · simpa [bool.true, true] using h1

lemma eta {X : C} (f : 𝟮 ⟶ X) : elim (false ≫ f) (true ≫ f) = f := by
  apply ext <;> simp [elim, true, false]

@[simp]
lemma elim_eta_left {X : C} (f : 𝟮 ⟶ X) : false ≫ elim (false ≫ f) (true ≫ f) = false ≫ f := by
  simp

@[simp] lemma elim_eta_right {X : C} (f : 𝟮 ⟶ X) :
    true ≫ elim (false ≫ f) (true ≫ f) = true ≫ f := by
  simp

/-- Two presentations with identical branch values are equal. -/
lemma mk_congr {X : C} {a a' b b' : 𝟙_ C ⟶ X}
    (h0 : a = a') (h1 : b = b') : elim a b = elim a' b' := by
  subst h0 h1
  rfl

@[simp]
lemma elim_comp {X : C} {a b : 𝟙_ C ⟶ X} {Y : C} (k : X ⟶ Y) :
    elim a b ≫ k = elim (a ≫ k) (b ≫ k) := by
  apply ext <;> simp [elim]

lemma elim_iff {X : C} {f : 𝟮 ⟶ X} {a b : 𝟙_ C ⟶ X} : elim a b = f ↔ (false ≫ f = a ∧ true ≫ f = b) := by
  constructor
  · intro h; subst h; simp
  · intro h; rcases h with ⟨h0, h1⟩
    apply ext
    · rw [false_elim]
      exact h0.symm
    · rw [true_elim]
      exact h1.symm

def constTrue : (𝟮 : C) ⟶ 𝟮 := elim true true

def constFalse : (𝟮 : C) ⟶ 𝟮 := elim false false

def toUnit : (𝟮 : C) ⟶ 𝟙_ C := elim (𝟙 _) (𝟙 _)

theorem constTrue_toUnit : constTrue ≫ toUnit (C:= C) = toUnit := by
  simp only [constTrue, elim_comp, toUnit]
  congr 1
  all_goals
  simp only [true_elim]

theorem constTrue_eq_toUnit_true : constTrue (C:= C) = bool.toUnit ≫ bool.true := by
  dsimp only [constTrue, toUnit, false, true]
  apply elim_iff.mpr
  simp

def not : (𝟮 : C) ⟶ 𝟮 := elim true false

def and [IsMonoidalLeftDistrib C] : (𝟮 : C) ⊗ 𝟮 ⟶ 𝟮 := sorry

theorem false_and [IsMonoidalLeftDistrib C] :
    (false ▷ (𝟮 : C)) ≫ and = (λ_ _).hom ≫ (desc inr inr) := by
  sorry

-- theorem false_and' [SemiCartesianMonoidalCategory C] :
--     (false ▷ (𝟮 : C)) ≫ and = SemiCartesianMonoidalCategory.constMorphism _ false := sorry

theorem true_and [IsMonoidalLeftDistrib C] : (true ▷ (𝟮 : C)) ≫ and = (λ_ _).hom := sorry

variable {X : C}

end bool

end MonoidalCategory

end CategoryTheory
