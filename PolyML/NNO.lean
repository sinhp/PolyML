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
import PolyML.ListArithmetic

import Mathlib

universe u v

namespace CategoryTheory

open Category Opposite Limits MonoidalCategory CartesianMonoidalCategory

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

open Endofunctor Algebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

-- SH: prec either for "parameterized" recursion or "primitive" recursion both are correct usage.
class IsNNO {N : C} (zero : 𝟙_ C ⟶ N) (succ : N ⟶ N) where
  prec {A B : C} (f : A ⟶ B) (g : B ⟶ B) : N ⊗ A ⟶ B
  zero_prec {A B : C} {f : A ⟶ B} {g : B ⟶ B} : (zero ▷ A) ≫ prec f g = (λ_ A).hom ≫ f
  succ_prec {A B : C} {f : A ⟶ B} {g : B ⟶ B} : (succ ▷ A) ≫ prec f g = prec f g ≫ g
  prec_uniq {A B : C} {f : A ⟶ B} {g : B ⟶ B} : ∀ r : N ⊗ A ⟶ B,
    (zero ▷ A) ≫ r = (λ_ A).hom ≫ f ∧ (succ ▷ A) ≫ r = r ≫ g → r = prec f g

namespace IsNNO

variable {N : C} {zero : 𝟙_ C ⟶ N} {succ : N ⟶ N} [IsNNO zero succ]

theorem congr_arg {A B : C} {f f' : A ⟶ B} {g g' : B ⟶ B}
    (h : f = f') (h' : g = g') :
    prec zero succ f g = prec zero succ f' g' := by
  subst h h'
  rfl

end IsNNO

variable (C)

/-- A natural number object in a monoidal category. -/
class Arithmetic where
  /-- The (left) natural number object. -/
  N : C
  /-- The zero morphism. -/
  zero : 𝟙_ C ⟶ N
  /-- The successor morphism. -/
  succ : N ⟶ N
  /-- The natural number object satisfies the properties of a left natural number object. -/
  [isNNO : IsNNO zero succ]

-- @[inherit_doc] notation "N_" => Arithmetic.N

namespace Arithmetic

open IsNNO

variable {C} [Arithmetic C] {A B : C}

instance : IsNNO (zero : 𝟙_ C ⟶ N) (succ : N ⟶ N) :=
  Arithmetic.isNNO

def prec (f : A ⟶ B) (g : B ⟶ B) : N ⊗ A ⟶ B :=
  IsNNO.prec zero succ f g

@[simp]
theorem zero_prec {f : A ⟶ B} {g : B ⟶ B} :
    (zero ▷ A) ≫ prec f g = (λ_ A).hom ≫ f := by
  apply IsNNO.zero_prec

theorem succ_prec {f : A ⟶ B} {g : B ⟶ B} :
    (succ ▷ A) ≫ prec f g = prec f g ≫ g := by
  apply IsNNO.succ_prec

theorem prec_precompose {A'} {u : A' ⟶ A} {f : A ⟶ B} {g : B ⟶ B} :
    N ◁ u ≫ prec f g = prec (u ≫ f) g := by
  apply prec_uniq
  constructor
  all_goals rw [← assoc, ← whisker_exchange, assoc]
  · rw [zero_prec]
    aesop
  · rw [succ_prec]
    aesop

/-- Iterates an endofunction a natural number of times. -/
def iter (f : A ⟶ A) : N ⊗ A ⟶ A := prec (𝟙 _) (f)

@[reassoc (attr := simp)]
theorem zero_iter {f : A ⟶ A} :
    zero ▷ A ≫ iter f = (λ_ A).hom := by
  simp [iter]

theorem succ_iter {f : A ⟶ A} :
    succ ▷ A ≫ iter f = iter f ≫ f := by
  simp [iter, succ_prec]

/-- `prec` can be reconstructed from `iter`. -/
@[reassoc (attr := simp)]
theorem iter_prec {f : A ⟶ B} {g : B ⟶ B} :
    (N ◁ f) ≫ iter g = prec f g := by
  apply prec_uniq
  constructor
  all_goals rw [← assoc, ← whisker_exchange, assoc]
  · rw [zero_iter]
    aesop
  · rw [succ_iter]
    aesop

/-- Addition of natural numbers. -/
def add : (N : C) ⊗ N ⟶ N :=
  prec (𝟙 _) (succ)

/-- The number one. -/
def one : 𝟙_ C ⟶ N :=
  zero ≫ succ

@[reassoc (attr := simp)]
theorem zero_add :
    zero ▷ (N : C) ≫ add = (λ_ N).hom := by
  simp [add]

theorem succ_add :
    succ ▷ (N : C) ≫ add = add ≫ succ := by
  simp [add, succ_prec]

theorem one_add_zero :
    (one ⊗ₘ zero) ≫ add = (λ_ (𝟙_ C)).hom ≫ one := by
  rw [tensorHom_def']
  simp only [id_whiskerLeft, assoc, Iso.cancel_iso_hom_left]
  dsimp [add]
  unfold one
  sorry

theorem zero_add_one :
    (zero ⊗ₘ one) ≫ add = (λ_ (𝟙_ C)).hom ≫ one := by
  sorry

-- commutativity of addition
theorem add_comm [BraidedCategory C] :
    (β_ (N : C) N).hom ≫ add = add := by
  sorry

-- associativity of addition
theorem add_assoc [BraidedCategory C] :
    add ▷ (N : C) ≫ add = (α_ _ _ _).hom ≫ (N ◁ add) ≫ add := by
  dsimp [add]
  sorry

def iterCurried [Closed A] [BraidedCategory C] (f : A ⟶ A) : N ⟶ (A ⟶[C] A) :=
  (MonoidalClosed.curry <| (β_ _ _).hom ≫ iter f)

end Arithmetic

open Arithmetic

/-- Every list-arithmetic category has a natural number object. -/
@[simps]
instance arithmeticOfListArithmetic [ListArithmetic C] : Arithmetic C where
  N := list (𝟙_ C)
  zero := list.nil
  succ := (λ_ _).inv ≫ list.cons (A:= 𝟙_ C)
  isNNO := {
    prec e a := list.prec e ((λ_ _).hom ≫ a)
    zero_prec := by {
      intros A B f g
      rw [list.nil_prec]
    }-- list.nil_prec
    succ_prec {A B f g}:= by
      rw [comp_whiskerRight, assoc]
      rw [list.cons_prec]
      sorry
    prec_uniq := by {
      rintro A B f g r ⟨hnil, hcons⟩
      --rw [← list.prec_uniq]
      sorry
      }
  }

namespace list

variable {C} [ListArithmetic C]

/-- The length of a list. -/
def len (isTerminalTensorUnit : IsTerminal (𝟙_ C) := by aesop) {A : C} : list A ⟶ N :=
  list.map <| isTerminalTensorUnit.from A

namespace length

variable (h : IsTerminal (𝟙_ C))

def toUnit (A : C) : A ⟶ 𝟙_ C := h.from _

variable {A : C}

theorem cons_len_eq_map_toUnit_cons {A : C} : list.cons ≫ list.len h =
    A ◁ list.map (toUnit h A) ≫ (toUnit h A ▷ list (𝟙_ C)) ≫ list.cons (A := 𝟙_ C) := by
  dsimp [list.len, list.cons, list.map]
  rw [plist.cons_map]
  rfl

@[reassoc (attr := simp)]
theorem nil_len_zero : list.nil (A:= A) ≫ list.len = zero := by
  simp [len]
  rfl

-- len (a :: xs) = succ (len xs)
theorem cons_len_succ :
    list.cons ≫ list.len = (toUnit h A ⊗ₘ list.len) ≫ (λ_ N).hom ≫ succ := by
  dsimp [list.len]
  rw [list.cons_map]
  rw [← Category.assoc]
  rw [tensorHom_def']
  congr 1
  simp_all only [Iso.hom_inv_id_assoc]

set_option diagnostics true
-- len ([x]) = 1
theorem singleton_len_one :
    list.singleton ≫ list.len = toUnit h A ≫ one := by
  dsimp [len, singleton, toUnit, one]
  sorry

end length

end list

end CategoryTheory
