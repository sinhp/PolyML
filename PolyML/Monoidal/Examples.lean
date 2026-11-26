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
    elim x y := fun b => bif b then y () else x ()
    ff_elim := by intros; funext u; rfl
    tt_elim := by intros; funext u; rfl
    elim_uniq := by
      intro X a b f h0 h1
      funext u
      cases u with
      | true => exact congrFun h1 ()
      | false => exact congrFun h0 ()
  }

instance boolType : Bool (Type u) where
  obj := ULift Bool
  ff := fun _ => ULift.up false
  tt := fun _ => ULift.up true
  isBool := {
    elim x y := fun b => if b.down then y ⟨⟩ else x ⟨⟩
    ff_elim := by intros; funext u; rfl
    tt_elim := by intros; funext u; rfl
    elim_uniq := by
      intro X a b f h0 h1
      funext u
      obtain ⟨bb⟩ := u
      cases bb with
      | true => exact congrFun h1 ⟨⟩
      | false => exact congrFun h0 ⟨⟩
  }

instance pnnoType₀ : PNNO (Type) where
  N := ℕ
  zero := fun _ => 0
  succ := Nat.succ
  isPNNO := {
    prc {P B} b g := fun x => Nat.rec (b x.2) (fun _ b => g b) x.1
    zero_prc := by intros; funext ⟨_, p⟩; rfl
    succ_prc := by intros; funext ⟨n, p⟩; rfl
    prc_uniq := by
      intro P B f g r h_zero h_succ
      funext ⟨n, p⟩
      induction n with
      | zero => exact congrFun h_zero ((), p)
      | succ n ih =>
        have hs := congrFun h_succ (n, p)
        exact hs.trans (congrArg g ih)
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
    prc := fun {P B} b g => fun x => Nat.rec (b x.2) (fun _ b => g b) x.1.down
    zero_prc := by intros; funext ⟨_, p⟩; rfl
    succ_prc := by intros; funext ⟨n, p⟩; rfl
    prc_uniq := by
      intro P B f g r h_zero h_succ
      funext ⟨⟨n⟩, p⟩
      induction n with
      | zero => exact congrFun h_zero (⟨⟩, p)
      | succ n ih =>
        have hs := congrFun h_succ (⟨n⟩, p)
        exact hs.trans (congrArg g ih)
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
      induction l with
      | nil =>
        simpa using congrFun h_nil (PUnit.unit, p)
      | cons head tail ih =>
        have hc := congrFun h_cons (head, tail, p)
        simp only [tensor_apply, whiskerRight_apply, associator_inv_apply,
          whiskerLeft_apply, types_comp_apply] at hc
        simp only [List.foldr]
        rw [hc, ih]
        rfl
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
      induction l with
      | nil =>
        simpa using congrFun h_nil (PUnit.unit, p)
      | cons head tail ih =>
        have hc := congrFun h_cons (head, tail, p)
        simp only [tensor_apply, whiskerRight_apply, associator_inv_apply,
          whiskerLeft_apply, types_comp_apply] at hc
        simp only [List.foldr]
        rw [hc, ih]
        rfl
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
      { app := fun X => Nat.rec (b.app X ()) (fun _ b => g.app X b)
        naturality := by
          intro X Y f
          funext n
          show Nat.rec (b.app Y ()) (fun _ b => g.app Y b) n
              = B.map f (Nat.rec (b.app X ()) (fun _ b => g.app X b) n)
          induction n with
          | zero =>
            have hb := congrFun (b.naturality f) PUnit.unit
            exact hb
          | succ n ih =>
            have hg := congrFun (g.naturality f)
              (Nat.rec (b.app X ()) (fun _ b => g.app X b) n)
            simp only [types_comp_apply] at hg
            show g.app Y _ = B.map f (g.app X _)
            rw [ih, hg] }
    zero_rc := by
      intro B b g
      ext X u
      rfl
    succ_rc := by
      intro B b g
      ext X n
      rfl
    rc_uniq := by
      intro B b g r h_zero h_succ
      ext X n
      induction n with
      | zero =>
        have h0 := congrFun (NatTrans.congr_app h_zero X) PUnit.unit
        exact h0
      | succ n ih =>
        have hs := congrFun (NatTrans.congr_app h_succ X) n
        simp only [NatTrans.comp_app, types_comp_apply] at hs
        exact hs.trans (congrArg (g.app X) ih)
  }

instance pnnoPresheaf {C : Type u} [Category C] : PNNO (C ⥤ Type) where
  N := (Functor.const (J:= C)).obj ℕ
  zero := (Functor.const (J:= C)).map (fun _ => 0)
  succ := (Functor.const (J:= C)).map Nat.succ
  isPNNO := {
    prc := fun {P B} b g =>
      { app := fun X => fun (np : ℕ × P.obj X) =>
          Nat.rec (b.app X np.2) (fun _ b => g.app X b) np.1
        naturality := by
          intro X Y h
          funext ⟨n, p⟩
          show Nat.rec (b.app Y (P.map h p)) (fun _ b => g.app Y b) n
              = B.map h (Nat.rec (b.app X p) (fun _ b => g.app X b) n)
          induction n with
          | zero =>
            have hb := congrFun (b.naturality h) p
            exact hb
          | succ n ih =>
            have hg := congrFun (g.naturality h)
              (Nat.rec (b.app X p) (fun _ b => g.app X b) n)
            simp only [types_comp_apply] at hg
            show g.app Y _ = B.map h (g.app X _)
            rw [ih, hg] }
    zero_prc := by
      intro P B b g
      ext X ⟨u, p⟩
      rfl
    succ_prc := by
      intro P B b g
      ext X ⟨n, p⟩
      rfl
    prc_uniq := by
      intro P B b g r h_zero h_succ
      ext X ⟨n, p⟩
      induction n with
      | zero =>
        exact congrFun (NatTrans.congr_app h_zero X) (PUnit.unit, p)
      | succ n ih =>
        have hs := congrFun (NatTrans.congr_app h_succ X) (n, p)
        simp only [NatTrans.comp_app, types_comp_apply, whiskerRight_apply] at hs
        exact hs.trans (congrArg (g.app X) ih)
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
        intro X Y h
        funext ⟨l, p⟩
        show List.foldr (g.app Y).curry (f.app Y (P.map h p)) (List.map (A.map h) l)
            = B.map h (List.foldr (g.app X).curry (f.app X p) l)
        induction l with
        | nil =>
          exact congrFun (f.naturality h) p
        | cons head tail ih =>
          have hg : g.app Y (A.map h head,
              B.map h (List.foldr (g.app X).curry (f.app X p) tail))
            = B.map h (g.app X (head, List.foldr (g.app X).curry (f.app X p) tail)) := by
            have := congrFun (g.naturality h)
              (head, List.foldr (g.app X).curry (f.app X p) tail)
            simpa [Monoidal.tensorObj_map] using this
          show g.app Y (A.map h head, _) = B.map h (g.app X (head, _))
          rw [ih, hg]
    }
    nil_prc := by
      intro P B f g
      ext X ⟨u, p⟩
      rfl
    cons_prc := by
      intro P B f g
      ext X ⟨a, l, p⟩
      rfl
    prc_uniq := by
      intro P B f g r h_nil h_cons
      ext X ⟨l, p⟩
      induction l with
      | nil =>
        exact congrFun (NatTrans.congr_app h_nil X) (PUnit.unit, p)
      | cons head tail ih =>
        have hc := congrFun (NatTrans.congr_app h_cons X) (head, tail, p)
        simp only [NatTrans.comp_app, types_comp_apply,
          Monoidal.whiskerRight_app, Monoidal.whiskerLeft_app,
          Monoidal.associator_inv_app,
          associator_inv_apply, associator_inv_apply_1_1, associator_inv_apply_1_2,
          associator_inv_apply_2,
          whiskerRight_apply, whiskerLeft_apply,
          tensor_apply, Function.curry_apply] at hc
        show r.app X (head :: tail, p) = g.app X (head, _)
        rw [hc, ih]
  }}

-- make a test case for computing the length of a list in presheaf category

section

open SimplexCategory Simplicial Category Opposite

variable (n : ℕ)

attribute [local instance] listPresheaf

#check PList.L ((yoneda.obj (⦋n⦌ : SimplexCategory)))

def simplicesListIso (m : ℕ) :
    (PList.L ((yoneda.obj (⦋n⦌ : SimplexCategory))) |>.obj (op ⦋m⦌)) ≅ List (⦋m⦌ ⟶ ⦋n⦌) :=
  Iso.refl _


end

#check yoneda
#check isRepresentable_of_natIso

-- We want to prove that categorical fin operations correspond to the arithmetical ones in Types.

-- #check List.cons



end CategoryTheory
