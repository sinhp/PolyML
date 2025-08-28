/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Data.PNat.Notation

/-! # Powers of an object in a monoidal category

TODO : show that the powers of an object in a monoidal category form a monoidal category.
-/

namespace CategoryTheory

open Category CategoryTheory Functor MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace MonoidalCategory

-- @[expose]
-- def iteratedTensor : Nat → C → C
--   | 0, _ => 𝟙_ C
--   | n + 1, A =>  iteratedTensor n A ⊗ A


-- def powNat (e : C ≌ C) : ℕ → (C ≌ C)
--   | 0 => Equivalence.refl
--   | 1 => e
--   | n + 2 => e.trans (powNat e (n + 1))

@[expose]
def iteratedTensor : Nat → C → C
  | 0, A => 𝟙_ C
  | 1 , A => A
  | n + 2, A =>  A ⊗ iteratedTensor (n + 1) A

def pow : ℕ → C → C := iteratedTensor

scoped notation  A "^[" n "]" => pow n A

def powZeroIso (A : C) : A^[0] ≅ 𝟙_ C := Iso.refl _

def powSuccEq (A : C) (n : ℕ) (h : 0 < n) : A ^[(n + 1)] = A ⊗ A ^[n] := by
  dsimp [pow]
  cases n with
  | zero => aesop
  | succ =>
  simp_all only [Nat.zero_lt_succ]
  rfl

def powSuccIso' (A : C) (n : ℕ) (h : 0 < n := by aesop) : A ^[(n + 1)] ≅ A ⊗ A ^[n] :=
  eqToIso <| powSuccEq A n h

def powSuccIso (A : C) (n : ℕ)  : A ^[(n + 1)] ≅ A ⊗ A^[n] := by
  match n with
  | Nat.zero => exact (ρ_ A).symm
  | Nat.succ k => exact powSuccIso' A (k + 1)

def powOneIso (A : C) : A^[1] ≅ A := Iso.refl _

def powTwoIso (A : C) : A^[2] ≅ A ⊗ A := Iso.refl _ --whiskerRightIso (powOneIso A) A

def powThreeIso (A : C) : A^[3] ≅ A ⊗ A ⊗ A := Iso.refl _ --whiskerRightIso (powTwoIso A) A


end MonoidalCategory

end CategoryTheory
