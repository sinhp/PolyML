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

@[expose]
def iteratedTensor : Nat → C → C
  | 0, A => A
  | n + 1, A =>  A ⊗ iteratedTensor n A


def pow : ℕ → C → C := fun n  A => if n = 0 then 𝟙_ C else iteratedTensor (n - 1) A

scoped notation  A "^[" n "]" => pow n A

-- theorem pow_zero (A : C) : A ^ 0 = 𝟙_ C := rfl

-- def powZeroIso (A : C) : A ^ 0 ≅ 𝟙_ C := Iso.refl _

def powZeroIso (A : C) : A ^[0] ≅ 𝟙_ C := Iso.refl _

def powSuccEq (A : C) (n : ℕ) (h : 0 < n) : A ^[(n + 1)] = A ⊗ A ^[n] := by
  dsimp [pow]
  cases n with
  | zero => aesop
  | succ =>
  simp_all only [Nat.zero_lt_succ, Nat.add_eq_zero, Nat.succ_ne_self, and_false, ↓reduceIte, Nat.add_one_sub_one]
  rfl
  --rw [Nat.sub_succ, if_pos (Nat.succ_ne_zero _), iteratedTensor]

def powSuccIso (A : C) (n : ℕ) (h : 0 < n := by aesop) : A ^[(n + 1)] ≅ A ⊗ A ^[n] :=
  eqToIso <| powSuccEq A n h

def powOneIso (A : C) : A ^[1] ≅ A := Iso.refl _

def powTwoIso (A : C) : A ^[2] ≅ A ⊗ A := Iso.refl _ --whiskerRightIso (powOneIso A) A

def powThreeIso (A : C) : A ^[3] ≅ A ⊗ A ⊗ A := Iso.refl _ --whiskerRightIso (powTwoIso A) A


end MonoidalCategory

end CategoryTheory
