/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Monoidal.Comon_
import PolyML.Monoidal.ListArithmetic
import PolyML.ForMathlib.Monoidal.Powers
import PolyML.ForMathlib.Monoidal.SemiCartesian
import Mathlib.Tactic.CategoryTheory.Coherence
import PolyML.ForMathlib.Bool

universe u v

namespace CategoryTheory

open Category Opposite MonoidalCategory Limits

-- attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

variable {C : Type u} [Category.{v} C]

-- SH: prec for "parameterized" recursion.
-- SH: usually params are on the left, although this becomes incompatible with plist.
class IsNNO [MonoidalCategory C] {N : C} (zero : 𝟙_ C ⟶ N) (succ : N ⟶ N) where
  prec {P B : C} (f : P ⟶ B) (g : B ⟶ B) : N ⊗ P ⟶ B
  zero_prec {P B : C} {f : P ⟶ B} {g : B ⟶ B} : (zero ▷ P) ≫ prec f g = (λ_ P).hom ≫ f
  succ_prec {P B : C} {f : P ⟶ B} {g : B ⟶ B} : (succ ▷ P) ≫ prec f g = prec f g ≫ g
  prec_uniq {P B : C} {f : P ⟶ B} {g : B ⟶ B} (r : N ⊗ P ⟶ B)
  (h_zero : (zero ▷ P) ≫ r = (λ_ P).hom ≫ f) (h_succ: (succ ▷ P) ≫ r = r ≫ g) : r = prec f g

namespace IsNNO

variable [MonoidalCategory C]

variable {N : C} {zero : 𝟙_ C ⟶ N} {succ : N ⟶ N} [IsNNO zero succ]

theorem congr_arg {A B : C} {f f' : A ⟶ B} {g g' : B ⟶ B}
    (h : f = f') (h' : g = g') :
    prec zero succ f g = prec zero succ f' g' := by
  subst h h'
  rfl

/-- Any two natural number objects in a monoidal category are isomorphic. -/
def iso {N N' : C} {zero : 𝟙_ C ⟶ N} {succ : N ⟶ N} {zero' : 𝟙_ C ⟶ N'} {succ' : N' ⟶ N'}
    [IsNNO zero succ] [IsNNO zero' succ'] : N ≅ N' where
  hom := (ρ_ N).inv ≫ prec zero succ zero' succ'
  inv := (ρ_ N').inv ≫ prec zero' succ' zero succ
  hom_inv_id := sorry
  inv_hom_id := sorry

end IsNNO

variable (C)

/-- A natural number object in a monoidal category. -/
class NNO [MonoidalCategory C] where
  /-- The (left) natural number object. -/
  N : C
  /-- The zero morphism. -/
  zero : 𝟙_ C ⟶ N
  /-- The successor morphism. -/
  succ : N ⟶ N
  /-- The natural number object satisfies the properties of a left natural number object. -/
  [isNNO : IsNNO zero succ]

-- @[inherit_doc] notation "N_" => NNO.N

def nno (C : Type u) [Category.{v} C] [MonoidalCategory C] [NNO C] : C := NNO.N

namespace NNO

open IsNNO

variable {C} [MonoidalCategory C] [NNO C] {P B : C}

instance : IsNNO (zero : 𝟙_ C ⟶ N) (succ : N ⟶ N) :=
  NNO.isNNO

def prec (f : P ⟶ B) (g : B ⟶ B) : N ⊗ P ⟶ B :=
  IsNNO.prec zero succ f g

@[simp]
theorem zero_prec {f : P ⟶ B} {g : B ⟶ B} :
  (zero ▷ P) ≫ prec f g = (λ_ P).hom ≫ f := by
  apply IsNNO.zero_prec

theorem succ_prec {f : P ⟶ B} {g : B ⟶ B} :
  (succ ▷ P) ≫ prec f g = prec f g ≫ g := by
  apply IsNNO.succ_prec

theorem prec_precompose {P'} {u : P' ⟶ P} {f : P ⟶ B} {g : B ⟶ B} :
  N ◁ u ≫ prec f g = prec (u ≫ f) g := by
  apply prec_uniq
  all_goals rw [← assoc, ← whisker_exchange, assoc]
  · rw [zero_prec]
    aesop
  · rw [succ_prec]
    aesop

theorem prec_postcompose {B'} {f : P ⟶ B} {g : B ⟶ B} {g' : B' ⟶ B'} (d : B ⟶ B') :
    prec f g ≫ d = prec (f ≫ d) g' := by
  sorry

/-- Iterates an endomorphism `n` times. -/
def iter (f : P ⟶ P) : N ⊗ P ⟶ P := prec (𝟙 _) (f)

/-- Recursion with the parameter `A` set to the unit object `𝟙_ C` -/
def urec (f : 𝟙_ C ⟶ B) (g : B ⟶ B) : N ⟶ B :=
  (ρ_ _).inv ≫ prec f g

@[reassoc (attr := simp)]
theorem zero_iter {f : P ⟶ P} :
  zero ▷ P ≫ iter f = (λ_ P).hom := by
  simp [iter]

theorem succ_iter {f : P ⟶ P} :
  succ ▷ P ≫ iter f = iter f ≫ f := by
  simp [iter, succ_prec]

/-- `prec` can be reconstructed from `iter`. -/
@[reassoc (attr := simp)]
theorem iter_prec {f : P ⟶ B} {g : B ⟶ B} : (N ◁ f) ≫ iter g = prec f g := by
  simpa using prec_precompose (u:= f) (f:= 𝟙 B) (g:= g)

theorem eq_whisker_iter {f : P ⟶ B} {g : B ⟶ B} (r : N ⊗ P ⟶ B)
    (h_zero : (zero ▷ P) ≫ r = (λ_ P).hom ≫ f) (h_succ : (succ ▷ P) ≫ r = r ≫ g) :
    r = (N ◁ f) ≫ iter g := by
  rw [iter_prec]
  apply IsNNO.prec_uniq
  all_goals
  assumption

-- SH : rfpi coherence
lemma prec_zero_succ_eq_rightUnitor : prec (P := 𝟙_ C) (B := N) zero succ = (ρ_ N).hom := by
  symm
  apply IsNNO.prec_uniq
  · coherence
  · apply rightUnitor_naturality succ

/-- The number one. -/
def one : 𝟙_ C ⟶ N := zero ≫ succ

def const (X : C) (x : 𝟙_ C ⟶ X) : N ⟶ X := (ρ_ _).inv ≫ prec x (𝟙 X)

def toUnit : N ⟶ 𝟙_ C := (ρ_ _).inv ≫ iter (𝟙 _)

theorem const_toUnit (X : C) (x : 𝟙_ C ⟶ X) : const X x = toUnit ≫ x := by
  dsimp [const, toUnit]
  simp only [assoc, Iso.cancel_iso_inv_left]
  apply Eq.symm
  apply prec_uniq
  · rw [← assoc]; rw [zero_iter]
  · rw [← assoc]; rw [succ_iter]; simp only [comp_id]

open bool coprod

variable (C)

noncomputable def toBool [HasBinaryCoproducts C] : (N : C) ⟶ 𝟮 :=
  (ρ_ _).inv ≫ prec inl (desc inr inr)

noncomputable def fromBool [HasBinaryCoproducts C] : 𝟮 ⟶ (N : C) := bool.elim zero one

variable {C}

theorem toBool_zero [HasBinaryCoproducts C] :
    zero ≫ toBool C = bool.false := by
  dsimp [toBool]
  rw [← assoc, rightUnitor_inv_naturality]
  rw [assoc, zero_prec]
  dsimp [bool.false]
  refine (Iso.inv_comp_eq (ρ_ (𝟙_ C))).mpr ?_
  refine ?_ =≫ _
  exact unitors_equal

theorem toBool_succ [HasBinaryCoproducts C] :
    succ ≫ toBool C = toUnit ≫ bool.true := by
  dsimp [toBool, bool.true, toUnit]
  rw [← assoc, rightUnitor_inv_naturality, assoc]
  rw [succ_prec, prec_postcompose]
  dsimp [iter]
  rw [assoc, prec_postcompose]
  simp only [colimit.ι_desc, BinaryCofan.mk_pt,
    BinaryCofan.ι_app_left, BinaryCofan.mk_inl, id_comp, Iso.cancel_iso_inv_left]
  congr
  exact 𝟙 𝟮

theorem fromBool_false [HasBinaryCoproducts C] :
    bool.false ≫ fromBool C = zero := by
  dsimp [bool.false, fromBool, elim]
  simp only [colimit.ι_desc, BinaryCofan.mk_pt,
    BinaryCofan.ι_app_left, BinaryCofan.mk_inl]

theorem fromBool_true [HasBinaryCoproducts C] :
    bool.true ≫ fromBool C = one := by
  dsimp [bool.true, fromBool, elim]
  simp only [colimit.ι_desc, BinaryCofan.mk_pt,
    BinaryCofan.ι_app_right, BinaryCofan.mk_inr]

theorem fromBool_toBool [HasBinaryCoproducts C] :
    fromBool C ≫ toBool C = 𝟙 (𝟮 : C) := by
  apply bool.ext
  · dsimp [bool.false, fromBool, elim, toBool]
    simp only [desc_comp, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.ι_app_left,
      BinaryCofan.mk_inl, comp_id]
    rw [← assoc, rightUnitor_inv_naturality, assoc, zero_prec]
    simp only [unitors_equal, Iso.inv_hom_id_assoc]
  · dsimp [bool.true, fromBool, elim, toBool, one]
    simp only [desc_comp, assoc, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.ι_app_right,
      BinaryCofan.mk_inr, comp_id]
    rw [← assoc, ← assoc, rightUnitor_inv_naturality]
    rw [assoc, comp_whiskerRight]
    simp only [assoc]
    rw [succ_prec]
    rw [← assoc (zero ▷ 𝟙_ C) (prec inl (desc inr inr)) (desc inr inr)]
    rw [zero_prec]
    simp only [assoc, colimit.ι_desc, BinaryCofan.mk_pt,
      BinaryCofan.ι_app_left, BinaryCofan.mk_inl]
    simp only [unitors_equal, Iso.inv_hom_id_assoc]

section Comon

variable [MonoidalCategory C] [NNO C]

def duplicate : (N : C) ⟶ N ⊗ N :=
  (ρ_ _).inv ≫ prec ((λ_ _).inv ≫ (zero ⊗ₘ zero)) (succ ⊗ₘ succ)

def delete : N ⟶ 𝟙_ C := (ρ_ _).inv ≫ iter (𝟙 _)

/-- The comonoid structure on the natural number object. -/
instance : Comon_Class (N : C) where
  counit := delete
  comul := duplicate
  counit_comul := by
    simp only [duplicate, delete]
    sorry
  comul_counit := sorry
  comul_assoc := sorry

variable (P)

def twist₀ : N^[0] ⊗ P ⟶ P ⊗ N^[0] := (λ_ P).hom ≫ (ρ_ P).inv

/-- The twist map induced by the universal property of the natural number object. -/
def twist₁ : N ⊗ P ⟶ P ⊗ N := prec ((ρ_ _ ).inv ≫ (P ◁ zero)) (P ◁ succ)

theorem twist₁_eq_rightUnitor_leftUnitor : twist₁ (𝟙_ C) = (ρ_ _).hom ≫ (λ_ _).inv := by
  dsimp [twist₁]
  apply Eq.symm
  apply prec_uniq
  · simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc, id_whiskerLeft]
    nth_rw 2 [← assoc, ← assoc]
    refine ?_ =≫ _
    rw [assoc, unitors_equal]
    simp only [Iso.inv_hom_id, comp_id]
  · simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc, id_whiskerLeft]

theorem twist₁_swap : twist₁ N = prec ((λ_ _).inv ≫ (zero ▷ (N : C))) (N ◁ succ) := by
  sorry

theorem twist₁_braiding [BraidedCategory C] {A : C} :
    twist₁ A = (β_ N A).hom := by
  dsimp [twist₁, prec]
  rw [← prec_uniq]
  · simp only [BraidedCategory.braiding_naturality_left,
      braiding_tensorUnit_left, assoc]
  · simp only [BraidedCategory.braiding_naturality_left]

theorem twist₁_is_iso {A : C} [BraidedCategory C] : IsIso (twist₁ A) := by
  rw [twist₁_braiding]
  simp only [Iso.hom_inv_id, Iso.inv_hom_id, and_self]

<<<<<<< HEAD:PolyML/Monoidal/NNO.lean
theorem twist₁_twist₁ : twist₁ N ≫ twist₁ N = 𝟙 (N ⊗ N : C) := by
  sorry
=======
theorem twist₁_twist₁ [BraidedCategory C] : twist₁ N ≫ twist₁ N = 𝟙 (N ⊗ N : C) := by
  nth_rw 1 [twist₁_braiding]
  refine (Iso.hom_comp_eq_id (β_ N N)).mpr ?_
  dsimp [twist₁]
  apply Eq.symm
  apply prec_uniq
  · simp only [BraidedCategory.braiding_inv_naturality_left,
    braiding_inv_tensorUnit_right, assoc]
  · simp only [BraidedCategory.braiding_inv_naturality_left]
>>>>>>> d14de57 (etc):PolyML/NNO.lean

def Twist : ℕ → Type v := fun k => (N^[k] ⊗ A ⟶ A ⊗ N^[k])

def twist : (k : ℕ) → Twist A k
  | 0 => twist₀ A
  | n + 1 => (powSuccIso N n).hom ▷ A ≫ (α_ N _ A).hom ≫ (N ◁ twist n) ≫ (α_ _ _ _).inv ≫
   (twist₁ A ▷ N^[n]) ≫ (α_ _ _ _).hom ≫ (A ◁ (powSuccIso N n).inv)

theorem twist_one : twist P 1 = twist₁ P := by
  sorry

end Comon

/-- Addition of natural numbers. -/
def add : (N : C) ⊗ N ⟶ N := iter succ

@[reassoc (attr := simp)]
theorem zero_add : zero ▷ (N : C) ≫ add = (λ_ N).hom := by
  simp [add]

theorem succ_add : succ ▷ (N : C) ≫ add = add ≫ succ := by
  simp [add, succ_iter]

theorem one_add_zero : (one ⊗ₘ zero) ≫ add = (λ_ (𝟙_ C)).hom ≫ one := by
  simp only [one, add, iter, one]
  rw [tensorHom_def, assoc, prec_precompose]
  refine (Iso.inv_comp_eq (λ_ (𝟙_ C))).mp ?_
  rw [comp_whiskerRight, assoc, succ_prec]
  rw [← assoc (zero ▷ 𝟙_ C) (prec (zero ≫ 𝟙 N) succ) succ]
  rw [zero_prec]
  simp only [comp_id, assoc, Iso.inv_hom_id_assoc]

theorem zero_add_one : (zero ⊗ₘ one) ≫ add = (λ_ (𝟙_ C)).hom ≫ one := by
  simp only [add, one, iter]
  rw [tensorHom_def, assoc, whiskerLeft_comp, assoc]
  rw [prec_precompose, prec_precompose, zero_prec]
  simp only [comp_id]

-- commutativity of addition
theorem add_comm [BraidedCategory C] : (β_ (N : C) N).hom ≫ add = add := by
  dsimp [add]
  nth_rw 2 [iter]
  apply prec_uniq
  · simp only [BraidedCategory.braiding_naturality_left_assoc,
      braiding_tensorUnit_left, iter_prec,
    assoc, comp_id]
    nth_rw 2 [← comp_id (f:= (λ_ N).hom)]
    refine (Iso.cancel_iso_hom_left (λ_ N) ((ρ_ N).inv ≫ prec zero succ) (𝟙 N)).mpr ?_
    refine (Iso.inv_comp_eq_id (ρ_ N)).mpr ?_
    apply Eq.symm
    apply prec_uniq
    simp only [whiskerRight_id, assoc, Iso.inv_hom_id, comp_id]
    refine ?_ =≫ _
    exact Eq.symm unitors_equal
    simp only [whiskerRight_id, assoc, Iso.inv_hom_id, comp_id]
  · simp only [BraidedCategory.braiding_naturality_left_assoc, iter_prec, assoc,
    Iso.cancel_iso_hom_left]
    apply Eq.symm
    apply prec_uniq
    · simp only [zero_iter_assoc]
    · rw [← assoc, succ_iter]

theorem add_zero [BraidedCategory C] : (N : C) ◁ zero ≫ add = (ρ_ N).hom := by
  rw [← add_comm]
  aesop

-- associativity of addition
theorem add_assoc :
    add ▷ (N : C) ≫ add = (α_ _ _ _).hom ≫ (N ◁ add) ≫ add := by
  dsimp [add]
  simp only [iter_prec]
  rw [← IsIso.inv_comp_eq]
  apply prec_uniq
  · simp only [whiskerRight_tensor, IsIso.Iso.inv_hom, assoc, Iso.hom_inv_id_assoc]
    rw [← assoc (zero ▷ N ▷ N) (iter succ ▷ N) (iter succ)]
    rw [← comp_whiskerRight, zero_iter]
    simp only [leftUnitor_whiskerRight, assoc, Iso.inv_hom_id_assoc]
  · simp only [whiskerRight_tensor, IsIso.Iso.inv_hom, assoc, Iso.hom_inv_id_assoc,
    Iso.cancel_iso_inv_left]
    rw [← assoc, ← comp_whiskerRight, succ_iter, comp_whiskerRight]
    rw [assoc, succ_iter]

/-- The monoid structure on the natural number object. -/
instance monClass [BraidedCategory C] : Mon_Class (N : C) where
  one := zero
  mul := add
  one_mul := zero_add
  mul_one := add_zero
  mul_assoc := add_assoc

instance [BraidedCategory C] : IsCommMon (N : C) where
  mul_comm := add_comm

def iterCurried {A : C} [Closed A] [BraidedCategory C] (f : A ⟶ A) : N ⟶ (A ⟶[C] A) :=
  (MonoidalClosed.curry <| (β_ _ _).hom ≫ iter f)

end NNO

open NNO

/-- Every list-arithmetic category has a natural number object. -/
@[simps]
instance arithmeticOfListArithmetic [MonoidalCategory C] [ListArithmetic C] : NNO C where
  N := list (𝟙_ C)
  zero := list.nil
  succ := (λ_ _).inv ≫ list.cons (A:= 𝟙_ C)
  isNNO := {
    prec {P B} e a := list.prec e ((λ_ _).hom ≫ a)
    zero_prec := by {
      intros A B f g; rw [list.nil_prec]}
    succ_prec {A B f g} := by
      rw [comp_whiskerRight, assoc]
      refine (IsIso.eq_inv_comp ((λ_ (list (𝟙_ C))).inv ▷ A)).mp ?_
      rw [list.cons_prec, ← assoc, ← assoc, ← assoc]
      refine ?_ =≫ g
      simp only [id_whiskerLeft, assoc,
        Iso.inv_hom_id, comp_id, leftUnitor_inv_whiskerRight,
        IsIso.inv_comp, IsIso.Iso.inv_inv]
    prec_uniq := by
     intros A B f g r hnil hcons
     apply list.prec_uniq r hnil
     simp only [comp_whiskerRight, leftUnitor_inv_whiskerRight, assoc] at hcons
     refine (Iso.inv_comp_eq (α_ (𝟙_ C) (list (𝟙_ C)) A)).mp ?_
     simp_all only [id_whiskerLeft, assoc, Iso.inv_hom_id_assoc]
     rw [← assoc]
     refine (Iso.inv_comp_eq (λ_ (list (𝟙_ C) ⊗ A))).mp ?_
     simpa only [assoc]
  }

namespace list

open Limits

variable {C} [SemiCartesianMonoidalCategory C] [ListArithmetic C]

/-- The length of a list. -/
def len {A : C} : list A ⟶ N :=
  list.map <| SemiCartesianMonoidalCategory.toUnit A

namespace length

open SemiCartesianMonoidalCategory

variable (h : IsTerminal (𝟙_ C))

variable {A : C}

theorem cons_len_eq_map_toUnit_cons {A : C} : list.cons ≫ list.len =
    A ◁ list.map (toUnit A) ≫ (toUnit A ▷ list (𝟙_ C)) ≫ list.cons (A := 𝟙_ C) := by
  dsimp [list.len, list.cons, list.map]
  rw [plist.cons_map]
  rfl

@[reassoc (attr := simp)]
theorem nil_len_zero : list.nil (A:= A) ≫ list.len = zero := by
  simp [len]
  rfl

-- len (a :: xs) = succ (len xs)
theorem cons_len_succ :
    list.cons ≫ list.len = (toUnit A ⊗ₘ list.len) ≫ (λ_ N).hom ≫ succ := by
  dsimp [list.len]
  rw [list.cons_map, ← Category.assoc, tensorHom_def']
  congr 1
  simp_all only [Iso.hom_inv_id_assoc]

set_option diagnostics true
-- len ([x]) = 1
theorem singleton_len_one :
    list.singleton ≫ list.len = toUnit A ≫ one := by
  sorry

end length

end list

namespace NNO

section const

variable {C} [SemiCartesianMonoidalCategory C] [NNO C]

open SemiCartesianMonoidalCategory

/-- `∀ n, f (succ n, a) = f (n, a)` implies `∀ n, f (n, a) = f (0, a)`. -/
theorem const_of_no_change_succ {A B : C} (r : N ⊗ A ⟶ B) (no_change_succ : succ ▷ A ≫ r = r) {n} :
    r = (constMorphism N n) ▷ A ≫ r := by
  dsimp [constMorphism]
  sorry

end const

namespace PR

open MorphismProperty CartesianMonoidalCategory

variable {C} [CartesianMonoidalCategory C] [NNO C]

open IsNNO

-- SH : rfpi coherence
lemma prec_zero_succ_eq_rightUnitor : prec (A := 𝟙_ C) (B := N) zero succ = (ρ_ N).hom := by
  symm
  apply IsNNO.prec_uniq
  · rw [unitors_equal]
    simp only [whiskerRight_id, assoc, Iso.inv_hom_id, comp_id]
  · apply rightUnitor_naturality succ

def fst_eq_prec {A : C} : fst N A = prec (constMorphism isTerminalTensorUnit A zero) succ := by
  apply prec_uniq
  · simp only [whiskerRight_fst]
    dsimp [constMorphism]
    rw [← assoc]
    refine ?_ =≫ _
    simp only [Limits.IsTerminal.comp_from]
    ext : 1
  · simp only [whiskerRight_fst]

/-- The diagonal morphism on an object `P`. -/
private def δ (X : C) : X ⟶ X ⊗ X :=
  lift (𝟙 X) (𝟙 X)

def uprimrecAux {X : C} (init : 𝟙_ C ⟶ X) (step : N ⊗ X ⟶ X) : N ⟶ N ⊗ X  :=
  (ρ_ _).inv ≫ prec ((λ_ _).inv ≫ (zero ⊗ₘ init)) (lift (fst N X ≫ succ) step)

theorem uprimrecAux_zero {X : C} (init : 𝟙_ C ⟶ X) (step : N ⊗ X ⟶ X) :
    zero ≫ uprimrecAux init step = (λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ init) := by
  dsimp [uprimrecAux]
  rw [← assoc, rightUnitor_inv_naturality, assoc,zero_prec]
  simp only [Iso.hom_inv_id_assoc]
  refine ?_ =≫ (zero ⊗ₘ init)
  aesop

theorem uprimrecAux_succ {X : C} (init : 𝟙_ C ⟶ X) (step : N ⊗ X ⟶ X) :
    succ ≫ uprimrecAux init step = uprimrecAux init step ≫  (lift (fst N X ≫ succ) step) := by
  simp only [uprimrecAux]
  rw [← assoc, rightUnitor_inv_naturality, assoc, succ_prec]
  simp only [comp_lift, assoc]

theorem uprimrecAux_fst {X : C} (init : 𝟙_ C ⟶ X) (step : N ⊗ X ⟶ X) :
    uprimrecAux init step ≫ fst N X = 𝟙 N := by
  sorry

def uprimrec {X : C} (init : 𝟙_ C ⟶ X) (step : N ⊗ X ⟶ X) : N ⟶ X :=
  uprimrecAux init step ≫ snd N X

theorem uprimrec_zero {X : C} (init : 𝟙_ C ⟶ X) (step : N ⊗ X ⟶ X) :
    zero ≫ uprimrec init step = init := by
  dsimp [uprimrec,uprimrecAux]
  rw [← assoc, ← assoc, rightUnitor_inv_naturality]
  rw [assoc, assoc]
  rw [Eq.symm (assoc (zero ▷ 𝟙_ C)
       (prec ((λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ init)) (lift (fst N X ≫ succ) step)) (snd N X))]
  rw [zero_prec]
  simp only [Iso.hom_inv_id_assoc, tensorHom_snd, rightUnitor_inv_snd_assoc]
  dsimp [CartesianMonoidalCategory.toUnit]
  simp only [IsTerminal.from_self, id_comp]

theorem uprimrec_succ {X : C} (init : 𝟙_ C ⟶ X) (step : N ⊗ X ⟶ X) :
    succ ≫ uprimrec init step = δ _ ≫ N ◁ (uprimrec init step) ≫ step := by
  sorry

/-- The helper morphism for defining primitive recursion. -/
def primrecAux {P B : C} (init : P ⟶ B) (step : N ⊗ P ⊗ B ⟶ B) : N ⊗ P ⟶ N ⊗ P ⊗ B :=
  prec ((λ_ _).inv ≫ ((𝟙_ C) ◁ (δ P)) ≫ (zero ⊗ₘ (𝟙 P) ⊗ₘ init ))
    ( lift (succ ⊗ₘ fst _ _) step ≫ (α_ N P B).hom )

/-- The full primitive recursion schema. -/
def primrec {P B : C} (init : P ⟶ B) (step : N ⊗ P ⊗ B ⟶ B) : N ⊗ P ⟶ B :=
  sorry

end PR

section operations

open CartesianMonoidalCategory PR Limits

variable {C} [CartesianMonoidalCategory C] [NNO C]

/-- The predecessor morphism. -/
def pred : (N : C) ⟶ N := uprimrec zero (fst N N)

open IsNNO

@[reassoc (attr := simp)]
theorem pred_zero : zero (C:= C) ≫ pred = zero := by
  simp [pred, uprimrec_zero]

@[reassoc (attr := simp)]
theorem pred_succ : succ (C:= C) ≫ pred = 𝟙 N := by
  simp only [pred, uprimrec_succ, δ, whiskerLeft_fst, lift_fst]

def sumUpTo : (N : C) ⟶ N := uprimrec (zero : 𝟙_ C ⟶ N) add

theorem sumUpTo_zero : zero ≫ sumUpTo (C:= C) = zero := by
  simp only [sumUpTo, uprimrec_zero]

-- theorem sumUpTo_succ : succ ≫ sumUpTo (C:= C) = sumUpTo (C:= C) ≫ add := by
--   sorry
>>>>>>> d1d64e4 (rebase):PolyML/NNO.lean

/-- The Subtraction morphism of natural numbers, truncated at `0`.-/
def sub : (N : C) ⊗ N ⟶ N := sorry

def eq' : (N : C) ⊗ N ⟶ N := sorry

variable (C)

noncomputable def bool [HasBinaryCoproducts C] := (𝟙_ C) ⨿ (𝟙_ C)

noncomputable def true [HasBinaryCoproducts C] : 𝟙_ C ⟶ bool C := coprod.inr

variable {C}

def eq [HasBinaryCoproducts C] : N ⊗ N ⟶ bool C := sorry

def lt [HasBinaryCoproducts C] : N ⊗ N ⟶ bool C := sorry

noncomputable def le [HasBinaryCoproducts C] : N ⊗ N ⟶ bool C :=
  (λ_ _).inv ≫ (zero ▷ (N ⊗ N)) ≫ (N ◁ sub) ≫ eq

theorem zero_le [HasBinaryCoproducts C] : (zero ▷ (N : C)) ≫ le = fst _ _ ≫ (true C) := by
  sorry

end operations

>>>>>>> 24eea14 (etc):PolyML/NNO.lean
end NNO

end CategoryTheory
