/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Monoidal.Category

/-! # Powers of an object in a monoidal category

TODO : show that the powers of an object in a monoidal category form a monoidal category.
-/

namespace CategoryTheory

open Category CategoryTheory Functor MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace MonoidalCategory

@[expose]
def iteratedTensor : Nat → C → C
  | 0, _ => 𝟙_ C
  | n + 1, A =>  iteratedTensor n A ⊗ A

@[simps]
instance : Pow C ℕ where
  pow A n := iteratedTensor n A

theorem pow_zero (A : C) : A ^ 0 = 𝟙_ C := rfl

def powZeroIso (A : C) : A ^ 0 ≅ 𝟙_ C := Iso.refl _

def powSuccIso (A : C) (n : ℕ) : A ^ (n + 1) ≅ A ^ n ⊗ A := Iso.refl _

def powOneIso (A : C) : A ^ 1 ≅ A := powSuccIso (A) 0 ≪≫ (λ_ A)

def powTwoIso (A : C) : A ^ 2 ≅ A ⊗ A := powSuccIso (A) 1 ≪≫ (whiskerRightIso (powOneIso A) A)

end MonoidalCategory

end CategoryTheory
