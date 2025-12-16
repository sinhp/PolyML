/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
import Mathlib.Data.FinEnum
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

import PolyML.Monoidal.List
import PolyML.Monoidal.Fin

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

@[simps]
def withPListType₀ : WithPList (Type) := fun A => {
  L := List A
  nil := fun _ => []
  cons := fun x => List.cons x.1 x.2
  isPList := {
    prc {P B} f g := fun x => List.foldr (g.curry) (f x.2) x.1
    nil_prc := by aesop
    cons_prc := by aesop
    prc_uniq {P B} f g r h_nil h_cons := by
      ext ⟨l, p⟩
      cases l with
      | nil =>
        simp
        symm
        simpa using congrArg (fun h => h (PUnit.unit, p)) (h_nil.symm)
      | cons head tail =>
        sorry
  }
}

@[simps!]
def withPListType : WithPList (Type u) := fun A => {
  L := List A
  nil := fun _ => []
  cons := fun x => List.cons x.1 x.2
  isPList := {
    prc {P B} f g := fun x => List.foldr (g.curry) (f x.2) x.1
    nil_prc := by aesop
    cons_prc := by aesop
    prc_uniq {P B} f g r h_nil h_cons := by
      ext ⟨l, p⟩
      cases l with
      | nil =>
        simp
        symm
        simpa using congrArg (fun h => h (PUnit.unit, p)) (h_nil.symm)
      | cons head tail =>
        sorry
  }
}

#check List.nil_len_zero

#check List.len (C:= Type)

#check withPListType₀ (ℕ)

#check (withPListType₀ ℕ).L

def myList : 𝟙_ (Type) ⟶  (withPListType₀ ℕ).L := fun _ => [1, 2, 3]

-- #eval myList PUnit.unit  -- fix this

-- #eval List.len myList

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

def listPresheaf {C : Type u} [Category C] : WithPList (C ⥤ Type) := fun A => {
  L.obj X := List (A.obj X)
  L.map {X Y} f := List.map (A.map f)
  nil.app X := fun _ => [ ]
  cons.app X := fun p => List.cons (α:= A.obj X) (p.1) (p.2)
  isPList := {
    prc {P B} f g := {
      app X := fun p => List.foldr (g.app X).curry (f.app X p.2) p.1
      naturality := by
        sorry
    }
    nil_prc := by
      sorry
    cons_prc := by
      sorry
    prc_uniq := by
      sorry
  }}


-- We want to prove that categorical fin operations correspond to the arithmetical ones in Types.

-- #check List.cons



end CategoryTheory
