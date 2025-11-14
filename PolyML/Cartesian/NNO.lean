/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import PolyML.Monoidal.NNO
import PolyML.ForMathlib.Monad.Distrib
import PolyML.ForMathlib.ConstantMorphism
-- import PolyML.ForMathlib.Monoidal.CoCartesian.Basic

/-!
# The Natural Numbers Object in Monoidal Categories
-/

universe u v

namespace CategoryTheory

open Category Opposite MonoidalCategory Limits IsNNO CartesianMonoidalCategory

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

namespace NNO

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [NNO C]

def mul' : (N : C) ⊗ N ⟶ N :=
  (prec (C:= C) ((λ_ _).inv ≫ zero ▷ N) (lift add (snd _ _))) ≫ (fst N N)

theorem zero_mul' : zero ▷ (N : C) ≫ mul' = fst _ _ ≫ zero := by
  simp [mul']
  sorry

-- SH: can the rhs be a simpler term involving `mul'`?
theorem succ_mul' :
    succ ▷ (N : C) ≫ mul' = (prec ((λ_ _).inv ≫ zero ▷ N) (lift add (snd _ _))) ≫ add := by
  simp [mul']
  sorry

theorem one_mul' : one ▷ (N : C) ≫ mul' = (λ_ _).hom := by
  sorry

theorem mul'_comm : (β_ N N).hom ≫ mul' = mul' (C:= C) := by
  sorry

-- instance semiring [ListArithmetic C] [WithBags C] : Semiring_ C := sorry

section PR

open MorphismProperty CartesianMonoidalCategory

def fst_eq_prec {A : C} : fst N A = prec (constMorphismFrom (𝟙_ C) (isTerminalTensorUnit) A zero) succ := by
  sorry

/-- The diagonal morphism on an object `X`. -/
private def δ' (X : C) : X ⟶ X ⊗ X :=
  lift (𝟙 X) (𝟙 X)

def uprimrecAux {X : C} (init : 𝟙_ C ⟶ X) (step : N ⊗ X ⟶ X) : N ⟶ N ⊗ X  :=
  (ρ_ _).inv ≫ prec ((λ_ _).inv ≫ (zero ⊗ₘ init)) (lift (fst N X ≫ succ) step)

theorem uprimrecAux_zero {X : C} (init : 𝟙_ C ⟶ X) (step : N ⊗ X ⟶ X) :
    zero ≫ uprimrecAux init step = (λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ init) := by
  simp only [uprimrecAux]
  sorry

theorem uprimrecAux_succ {X : C} (init : 𝟙_ C ⟶ X) (step : N ⊗ X ⟶ X) :
    succ ≫ uprimrecAux init step = uprimrecAux init step ≫ (lift (fst N X ≫ succ) step) := by
  simp only [uprimrecAux]
  sorry

theorem uprimrecAux_fst {X : C} (init : 𝟙_ C ⟶ X) (step : N ⊗ X ⟶ X) :
    uprimrecAux init step ≫ fst N X = 𝟙 N := by
  simp only [uprimrecAux]
  rw [fst_eq_prec]
  sorry

def uprimrec {X : C} (init : 𝟙_ C ⟶ X) (step : N ⊗ X ⟶ X) : N ⟶ X :=
  uprimrecAux init step ≫ snd N X

theorem uprimrec_zero {X : C} (init : 𝟙_ C ⟶ X) (step : N ⊗ X ⟶ X) :
    zero ≫ uprimrec init step = init := by
  simp [uprimrec, uprimrecAux]
  sorry

theorem uprimrec_succ {X : C} (init : 𝟙_ C ⟶ X) (step : N ⊗ X ⟶ X) :
    succ ≫ uprimrec init step = δ' _ ≫ N ◁ (uprimrec init step) ≫ step := by
  sorry

/-- The helper morphism for defining primitive recursion. -/
def primrecAux {P B : C} (init : P ⟶ B) (step : N ⊗ P ⊗ B ⟶ B) : N ⊗ P ⟶ N ⊗ P ⊗ B :=
  prec ((λ_ _).inv ≫ ((𝟙_ C) ◁ (δ' P)) ≫ (zero ⊗ₘ (𝟙 P) ⊗ₘ init ))
    ( lift (succ ⊗ₘ fst _ _) step ≫ (α_ N P B).hom )

/-- The full primitive recursion schema. -/
def primrec {P B : C} (init : P ⟶ B) (step : N ⊗ P ⊗ B ⟶ B) : N ⊗ P ⟶ B :=
  sorry

end PR

section operations

open Limits bool

/-- The predecessor morphism. -/
def pred : (N : C) ⟶ N := uprimrec zero (fst N N)

@[reassoc (attr := simp)]
theorem pred_zero : zero (C:= C) ≫ pred = zero := by
  simp only [pred, uprimrec, uprimrecAux]
  sorry

@[reassoc (attr := simp)]
theorem pred_succ : succ (C:= C) ≫ pred = 𝟙 N := by
  simp only [pred, uprimrec, uprimrecAux]
  sorry

def sumUpTo' : (N : C) ⟶ N := uprimrec (zero : 𝟙_ C ⟶ N) (add ≫ succ)

theorem sumUpTo'_zero : zero ≫ sumUpTo' (C:= C) = zero := by
  simp [sumUpTo']
  sorry

-- theorem sumUpTo_succ : succ ≫ sumUpTo (C:= C) = sumUpTo (C:= C) ≫ add := by
--   sorry

/-- The Subtraction morphism of natural numbers, truncated at `0`.-/
def sub' : (N : C) ⊗ N ⟶ N := sorry

/-- The maximum morphism on natural numbers.-/
def max' : (N : C) ⊗ N ⟶ N := (lift sub' (snd N N)) ≫ add

/-- The minimum morphism on natural numbers.-/
def min' : (N : C) ⊗ N ⟶ N := (lift add max') ≫ sub'

theorem max'_min'_add : lift max' min' ≫ add = add (C:= C) := by
  sorry

-- theorem sub_toBool [HasBinaryCoproducts C] :
--     sub ≫ toBool C = (toBool C ▷ (toBool C)) ≫ bool.and := by
--   sorry

def eqZero' : N ⟶ (N : C) := (λ_ _).inv ≫ (one ▷ N) ≫ sub'

theorem eqZero'_toBool_eq_toBool [HasBinaryCoproducts C] : eqZero' ≫ toBool C = toBool C := by
  simp [eqZero']
  sorry

/-- Testing for equality of two natural numbers.-/
def eq'Aux : (N : C) ⊗ N ⟶ N :=  lift (sub' ≫ eqZero') (twist₁ N ≫ sub' ≫ eqZero') ≫ min'

-- instance : CoCartesianMonoidalCategory C := sorry


-- SC
--   / \
-- C   CC
-- |
-- C + CC
-- issue: we now have two different monoidal strutures on C: one from cartesian monoidal and the other one
-- from co-cartesian monoidal. Lean is confused which one applies to `N`. IT should be the first one
-- and the second one should give computable coproducts.
-- this needs thinking.
noncomputable
def eq' [HasBinaryCoproducts C] : N ⊗ N ⟶ (𝟮 : C) := eq'Aux ≫ toBool C

noncomputable def le [HasBinaryCoproducts C] : N ⊗ N ⟶ (𝟮 : C) :=
  (λ_ _).inv ≫ (zero ▷ (N ⊗ N)) ≫ (N ◁ sub') ≫ eq'

/-- `lt m n` iff `le (succ m) n` .-/
noncomputable def lt [HasBinaryCoproducts C] : N ⊗ N ⟶ (𝟮 : C) :=
  (succ ▷ N) ≫ le

theorem zero_lt [HasBinaryCoproducts C] : zero ▷ (N : C) ≫ lt = fst _ _ ≫ true := by
  sorry

theorem zero_le [HasBinaryCoproducts C] : (zero ▷ (N : C)) ≫ le = fst _ _ ≫ true := by
  sorry



end operations


/-- The diagram `T_C ⟶ T_C ⨿ N ⟵  T_C ⨿ N`  defines an nno. -/


def colimitCocone (X : C) (h : IsTerminal X) : ColimitCocone (pair X N) where
  cocone := sorry
  isColimit := sorry


/-- The diagram `T_C ⟶ N ⟵ N` is a colimit diagram. -/
def BinaryCoproduct (X : C) (h : IsTerminal X): HasBinaryCoproduct X N where
  exists_colimit := sorry

end NNO

end CategoryTheory
