/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import PolyML.Monoidal.Fin
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
import Mathlib.Data.FinEnum
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

namespace CategoryTheory

open  MonoidalCategory

def boolType₀ : Bool (Type) where
  obj := Bool
  ff := fun _ => false
  tt := fun _ => true
  isBool := {
    elim x y := fun b => ite b (x ()) (y ())
    ff_elim := by sorry
    tt_elim := by sorry
    elim_uniq := by sorry
  }

def boolType : Bool (Type u) where
  obj := ULift Bool
  ff := fun _ => ULift.up false
  tt := fun _ => ULift.up true
  isBool := {
    elim x y := fun b => if b.down then x ⟨⟩ else y ⟨⟩
    ff_elim := by sorry
    tt_elim := by sorry
    elim_uniq := by sorry
  }

/-- The natural numbers object in the category `Type`. -/
def nnoType₀ : NNO (Type) where
  N := ℕ
  zero := fun _ => 0
  succ := Nat.succ
  isNNO := {
    rc {B} b g := Nat.rec (b ()) (fun n b => g b)
    zero_rc := by aesop
    succ_rc := by aesop
    rc_uniq := by sorry
  }

def pnnoType₀ : PNNO (Type) where
  N := ℕ
  zero := fun _ => 0
  succ := Nat.succ
  isPNNO := {
    prc {P B} b g := sorry --Nat.rec (b ()) (fun n b => g b)
    zero_prc := sorry
    succ_prc := sorry
    prc_uniq := sorry
  }

example : pnnoType₀.one = fun _ => (1 : ℕ) := rfl

#check list.nil_len_zero

#check list.len (C:= Type)

-- #eval list.len (C:= Type) ([1, 2, 3] : List ℕ)  -- fix this


def nnoType : NNO (Type u) where
  N := ULift ℕ
  zero := fun _ => ULift.up 0
  succ := fun n => ULift.up (Nat.succ n.down)
  isNNO := {
    rc := fun {B} b g => sorry
    zero_rc := sorry
    succ_rc := sorry
    rc_uniq := sorry
  }

def pnnoType : PNNO (Type u) where
  N := ULift ℕ
  zero := fun _ => ULift.up 0
  succ := fun n => ULift.up (Nat.succ n.down)
  isPNNO := {
    prc := fun {P B} b g => sorry
    zero_prc := sorry
    succ_prc := sorry
    prc_uniq := sorry
  }

/-- The NNO in presheaf categories. -/
def nnoPresheaf {C : Type u} [Category C] : NNO (C ⥤ Type) where
  N := (Functor.const (J:= C)).obj ℕ
  zero := (Functor.const (J:= C)).map (fun _ => 0)
  succ := (Functor.const (J:= C)).map Nat.succ
  isNNO := {
    rc := fun {B} b g =>
      { app := fun X => Nat.rec (b.app X ()) (fun n b => g.app X b)
        naturality := by
          sorry }
    zero_rc := sorry
    succ_rc := sorry
    rc_uniq := sorry
  }


-- We want to prove that categorical fin operations correspond to the arithmetical ones in Types.





end CategoryTheory
