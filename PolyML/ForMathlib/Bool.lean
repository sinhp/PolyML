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

namespace MonoidalCategory

variable [MonoidalCategory C] [HasBinaryCoproducts C]

def bool := (𝟙_ C) ⨿ (𝟙_ C)

namespace bool

open coprod

scoped notation "𝟮" => bool

def false : 𝟙_ C ⟶ 𝟮 := inl

def true : 𝟙_ C ⟶ 𝟮 := inr

def elim {X : C} (f : 𝟙_ C ⟶ X) (g : 𝟙_ C ⟶ X) : 𝟮 ⟶ X := desc f g

def and : (𝟮 : C) ⊗ 𝟮 ⟶ 𝟮 := sorry

theorem false_and : (false ▷ (𝟮 : C)) ≫ and = (λ_ _).hom ≫ (desc inr inr) := by
  sorry

-- theorem false_and' [SemiCartesianMonoidalCategory C] :
--     (false ▷ (𝟮 : C)) ≫ and = SemiCartesianMonoidalCategory.constMorphism _ false := sorry

theorem true_and : (true ▷ (𝟮 : C)) ≫ and = (λ_ _).hom := sorry



variable {X : C}

/-- Build a morphism `𝟮 ⟶ X` from its values on `false` and `true`. -/
def mk (f0 f1 : 𝟙_ C ⟶ X) : 𝟮 ⟶ X := bool.elim f0 f1

notation "⟪" f0 "," f1 "⟫" => mk f0 f1

@[simp] lemma false_mk (f0 f1 : 𝟙_ C ⟶ X) : false ≫ mk f0 f1 = f0 := by
  dsimp [mk, bool.false, false, elim]
  simp

@[simp] lemma true_mk (f0 f1 : 𝟙_ C ⟶ X) : true ≫ mk f0 f1 = f1 := by
  dsimp [mk, bool.true, true, elim]
  simp

@[simp] lemma elim_false {f0 f1 : 𝟙_ C ⟶ X} : false ≫ bool.elim f0 f1 = f0 := by
  dsimp [elim, bool.false, false]
  simp

@[simp] lemma elim_true {f0 f1 : 𝟙_ C ⟶ X} : true ≫ bool.elim f0 f1 = f1 := by
  dsimp [elim, bool.true, true]
  simp

/-- Extensionality for morphisms out of `𝟮`. -/
lemma ext {f g : 𝟮 ⟶ X}
    (h0 : false ≫ f = false ≫ g) (h1 : true ≫ f = true ≫ g) : f = g := by
  apply coprod.hom_ext
  · simpa [bool.false, false] using h0
  · simpa [bool.true, true] using h1

/-- Eta expansion: any `f : 𝟮 ⟶ X` is determined by its values on `false` and `true`. -/
lemma eta (f : 𝟮 ⟶ X) : mk (false ≫ f) (true ≫ f) = f := by
  apply ext <;> simp [mk]

@[simp] lemma mk_eta_left (f : 𝟮 ⟶ X) : false ≫ mk (false ≫ f) (true ≫ f) = false ≫ f := by
  simp

@[simp] lemma mk_eta_right (f : 𝟮 ⟶ X) : true ≫ mk (false ≫ f) (true ≫ f) = true ≫ f := by
  simp

/-- Two presentations with identical branch values are equal. -/
lemma mk_congr {a a' b b' : 𝟙_ C ⟶ X}
    (h0 : a = a') (h1 : b = b') : mk a b = mk a' b' := by
  subst h0 h1; rfl

@[simp] lemma mk_comp {a b : 𝟙_ C ⟶ X} {Y : C} (k : X ⟶ Y) :
    mk a b ≫ k = mk (a ≫ k) (b ≫ k) := by
  -- Compare on the two coproduct injections using ext.
  apply ext <;> simp [mk, elim]

/-- Any morphism from the coproduct is the elimination on its components (eta form expressed with `elim`). -/
@[simp] lemma elim_comp (f0 f1 : 𝟙_ C ⟶ X) : elim f0 f1 = mk f0 f1 := rfl

/-- Characterization: a morphism `f : 𝟮 ⟶ X` is equal to `mk a b` iff its restrictions agree. -/
lemma mk_iff {f : 𝟮 ⟶ X} {a b : 𝟙_ C ⟶ X} : mk a b = f ↔ (false ≫ f = a ∧ true ≫ f = b) := by
  constructor
  · intro h; subst h; simp
  · intro h; rcases h with ⟨h0, h1⟩
    apply ext
    · rw [false_mk]
      exact h0.symm
    · rw [true_mk]
      exact h1.symm

/-- Alternative form (symmetry of previous lemma). -/
lemma iff_mk {f : 𝟮 ⟶ X} {a b : 𝟙_ C ⟶ X} : f = mk a b ↔ (false ≫ f = a ∧ true ≫ f = b) := by
  simpa [eq_comm] using (mk_iff (f:= f) (a:= a) (b:= b))

end bool

end MonoidalCategory

end CategoryTheory
