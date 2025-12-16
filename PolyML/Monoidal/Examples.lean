/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
import Mathlib.Data.FinEnum
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.AlgebraicTopology.SimplexCategory.Defs

import PolyML.Monoidal.List
import PolyML.Monoidal.NNO
import PolyML.Monoidal.Fin

namespace CategoryTheory

open  MonoidalCategory

instance boolType₀ : Bool (Type) where
  obj := Bool
  ff := fun _ => false
  tt := fun _ => true
  isBool := {
    elim x y := fun b => ite b (x ()) (y ())
    ff_elim := by sorry
    tt_elim := by sorry
    elim_uniq := by sorry
  }

instance boolType : Bool (Type u) where
  obj := ULift Bool
  ff := fun _ => ULift.up false
  tt := fun _ => ULift.up true
  isBool := {
    elim x y := fun b => if b.down then x ⟨⟩ else y ⟨⟩
    ff_elim := by sorry
    tt_elim := by sorry
    elim_uniq := by sorry
  }

instance pnnoType₀ : PNNO (Type) where
  N := ℕ
  zero := fun _ => 0
  succ := Nat.succ
  isPNNO := {
    prc {P B} b g := fun x => Nat.rec (b x.2) (fun n b => g b) x.1
    zero_prc := sorry
    succ_prc := sorry
    prc_uniq := sorry
  }

instance nnoType₀ : NNO (Type) := NNO.ofPNNO

example : pnnoType₀.one = fun _ => (1 : ℕ) := rfl
example : nnoType₀.one = fun _ => (1 : ℕ) := rfl

#eval! pnnoType₀.one () -- fix this
#eval! nnoType₀.one () -- fix this

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

def nnoType : NNO (Type u) := @NNO.ofPNNO (Type u) _ _ pnnoType

@[simps]
instance withPListType₀ : WithPList (Type) := fun A => {
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

attribute [local instance] List.ofPList

instance withListType₀ : WithList (Type) := WithList.ofWithPList (C:= Type)


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

def withListType : WithList (Type u) :=
  @WithList.ofWithPList (C:= Type u) _ _ withPListType

#check (withPListType₀ ℕ).L

def myPList : 𝟙_ (Type) ⟶  (withPListType₀ ℕ).L := fun _ => [1, 2, 3]

def myList : 𝟙_ (Type) ⟶  (withListType₀ ℕ).L := fun _ => [1,2,3]

#eval! myPList PUnit.unit  -- fix this

#eval! List.len (C:= Type) ℕ (myList ())

#check PNNO.GlobalElement.num

-- #eval! PList.splitAt (C:= Type) (A:= ℕ) (PNNO.GlobalElement.num (Type) (3 : ℕ) (), myPList ())
--failed to compile definition, because it depends on 'PList.splitAt', which is noncomputable. HasBinaryProducts is noncomputable in Type. need to replace it with cocartesian monoidal category with computable coproducts.

/-- The NNO in presheaf categories. -/
instance nnoPresheaf {C : Type u} [Category C] : NNO (C ⥤ Type) where
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

instance pnnoPresheaf {C : Type u} [Category C] : PNNO (C ⥤ Type) where
  N := (Functor.const (J:= C)).obj ℕ
  zero := (Functor.const (J:= C)).map (fun _ => 0)
  succ := (Functor.const (J:= C)).map Nat.succ
  isPNNO := {
    prc := fun {P B} b g =>
      { app := fun X => sorry
        naturality := by
          sorry }
    zero_prc := sorry
    succ_prc := sorry
    prc_uniq := sorry
  }

instance listPresheaf {C : Type u} [Category C] : WithPList (C ⥤ Type) := fun A => {
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

-- make a test case for computing the length of a list in presheaf category

section

open SimplexCategory Simplicial Category Opposite

variable (n : ℕ)

attribute [local instance] listPresheaf

#check PList.L ((yoneda.obj (⦋n⦌ : SimplexCategory)))

def simplicesListIso (m : ℕ) :
    (PList.L ((yoneda.obj (⦋n⦌ : SimplexCategory))) |>.obj (op ⦋m⦌)) ≅ List (⦋m⦌ ⟶ ⦋n⦌) where
  hom := sorry
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry


end

#check yoneda
#check isRepresentable_of_natIso

-- We want to prove that categorical fin operations correspond to the arithmetical ones in Types.

-- #check List.cons



end CategoryTheory
