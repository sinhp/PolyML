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

def ttConst : 𝟮_ C ⟶ 𝟮_ C := elim tt tt

def ffConst : 𝟮_ C ⟶ 𝟮_ C := elim ff ff

def toUnit : 𝟮_ C ⟶ 𝟙_ C := elim (𝟙 _) (𝟙 _)

theorem ttConst_toUnit : ttConst ≫ toUnit (C:= C) = toUnit := by
  simp only [ttConst, elim_comp, toUnit]
  congr 1
  all_goals
  simp only [IsBool.tt_elim]

theorem ttConst_eq_toUnit_tt : ttConst (C:= C) = toUnit ≫ tt := by
  dsimp only [ttConst, toUnit, ffConst, ttConst]
  apply elim_iff.mpr
  simp

def not : 𝟮_ C ⟶ 𝟮_ C := elim tt ff

end Bool

open Bool

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasBinaryCoproducts C]

/-- A monoidal caetegory with binary coproducts has booleans. -/
@[simps]
def Bool.ofBinaryCoproduct : Bool C where
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

attribute [local instance] Bool.ofBinaryCoproduct

open Distributive

-- TODO (SH): It seem that we currently do not have any useful notation/macro for maps out of iterated coproducts. Here are some temporary macros.
-- The right thing is to have a small metaprogram that can generate these automatically detecting the pattern and the number of arguments/branches.

macro_rules
  |`(coprod.desc₃ $f1 $f2 $f3) => `(coprod.desc (coprod.desc $f1 $f2) $f3)

macro_rules
  |`(coprod.desc₄ $f1 $f2 $f3 $f4) => `(coprod.desc (coprod.desc₃ $f1 $f2 $f3) $f4)

macro_rules
  |`(coprod.desc₄' $f1 $f2 $f3 $f4) => `(coprod.desc (coprod.desc $f1 $f2) (coprod.desc $f3 $f4))

/-- The boolean "and" operation in a monoidal distributive category. -/
def Bool.and [HasBinaryCoproducts C] [IsMonoidalDistrib C] : 𝟮_ C ⊗ 𝟮_ C ⟶ 𝟮_ C  :=
  (∂L (𝟙_ C ⨿ 𝟙_ C) (𝟙_ C) (𝟙_ C)).inv ≫
  coprod.map
    (∂R (𝟙_ C) (𝟙_ C) (𝟙_ C)).inv
    (∂R (𝟙_ C) (𝟙_ C) (𝟙_ C)).inv ≫
  coprod.desc₄'
    ((λ_ _).hom ≫ Bool.ff)
    ((λ_ _).hom ≫ Bool.ff)
    ((λ_ _).hom ≫ Bool.ff)
    ((λ_ _).hom ≫ Bool.tt)

@[simp]
theorem Bool.and_def [HasBinaryCoproducts C] [IsMonoidalDistrib C] :
    and (C:= C) =
    (∂L (𝟙_ C ⨿ 𝟙_ C) (𝟙_ C) (𝟙_ C)).inv ≫
    coprod.map
      (∂R (𝟙_ C) (𝟙_ C) (𝟙_ C)).inv
      (∂R (𝟙_ C) (𝟙_ C) (𝟙_ C)).inv ≫
    coprod.desc
      (coprod.desc ((λ_ _).hom ≫ coprod.inl) ((λ_ _).hom ≫ coprod.inl))
      (coprod.desc ((λ_ _).hom ≫ coprod.inl) ((λ_ _).hom ≫ coprod.inr)) :=
  rfl

theorem ff_and [HasBinaryCoproducts C] [IsMonoidalDistrib C] :
    (ff ▷ (𝟮_ C)) ≫ and = (λ_ _).hom ≫ (elim (C:= C) (X:= 𝟮_ C) tt tt) := by
  sorry

theorem ff_and_ff [HasBinaryCoproducts C] [IsMonoidalDistrib C] :
    (ff ⊗ₘ ff) ≫ and (C:= C) = (λ_ _).hom ≫ ff := by
  sorry

theorem ff_and_tt [HasBinaryCoproducts C] [IsMonoidalDistrib C] :
    (ff ⊗ₘ tt) ≫ and (C:= C) = (λ_ _).hom ≫ ff := by
  sorry

theorem tt_and [HasBinaryCoproducts C] [IsMonoidalDistrib C] : (tt ▷ 𝟮_ C) ≫ and = (λ_ _).hom := sorry

theorem tt_and_ff [HasBinaryCoproducts C] [IsMonoidalDistrib C] :
    (tt ⊗ₘ ff) ≫ and (C:= C) = (λ_ _).hom ≫ ff := by
  sorry

theorem tt_and_tt [HasBinaryCoproducts C] [IsMonoidalDistrib C] :
    (tt ⊗ₘ tt) ≫ and (C:= C) = (λ_ _).hom ≫ tt := by
  sorry

end MonoidalCategory

end CategoryTheory
