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

theorem congr_arg {P B : C} {f f' : P ⟶ B} {g g' : B ⟶ B}
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
theorem prec_postcompose {B'} {f : P ⟶ B} {g : B ⟶ B} (g' : B' ⟶ B') (d : B ⟶ B')
    (comm_sq : CommSq g d d g' := by aesop) :
    prec f g ≫ d = prec (f ≫ d) g' := by

  apply prec_uniq
  · rw [← assoc, zero_prec]
    simp only [assoc]
  · rw [← assoc, succ_prec]
    simp only [assoc]
    refine _ ≫= ?_
    exact comm_sq.w

/-- Iterates an endomorphism `n` times. -/
def iter (f : P ⟶ P) : N ⊗ P ⟶ P := prec (𝟙 _) (f)

/-- Recursion with the parameter `P` set to the unit object `𝟙_ C` -/
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
  apply prec_uniq
  all_goals
  assumption

-- SH : rfpi coherence
lemma prec_zero_succ_eq_rightUnitor : prec (P := 𝟙_ C) (B := N) zero succ = (ρ_ N).hom := by
  symm
  apply prec_uniq
  · coherence
  · apply rightUnitor_naturality succ

/-- The morphism for number one, i.e. the successor of zero. -/
def one : 𝟙_ C ⟶ N := zero ≫ succ

/-- Maps any natural number to the fixed element `x`. -/
def const (X : C) (x : 𝟙_ C ⟶ X) : N ⟶ X := (ρ_ _).inv ≫ prec x (𝟙 X)

/-- Mapping the NNO to the unit of the monoidal category. -/
def toUnit : N ⟶ 𝟙_ C := (ρ_ _).inv ≫ iter (𝟙 (𝟙_ C))

@[reassoc (attr := simp)]
theorem zero_toUnit : zero ≫ toUnit = 𝟙 (𝟙_ C) := by
  rw [toUnit, ← assoc, rightUnitor_inv_naturality, assoc, zero_iter, unitors_equal]
  simp only [Iso.inv_hom_id]

theorem succ_toUnit : succ ≫ toUnit = toUnit (C:= C) := by
  rw [toUnit, ← assoc, rightUnitor_inv_naturality, assoc, succ_iter, comp_id]

@[simp]
theorem iter_id : iter (𝟙 P) = toUnit ▷ P ≫ (λ_ _).hom := by
  simp [iter, prec]
  symm
  apply prec_uniq
  · rw [← assoc, ← comp_whiskerRight, zero_toUnit, id_whiskerRight, id_comp, comp_id]
  · rw [← assoc, ← comp_whiskerRight, succ_toUnit, comp_id]

theorem iter_id_unit : iter (𝟙 (𝟙_ C)) = (ρ_ _).hom ≫ toUnit := by
  simp only [toUnit, Iso.hom_inv_id_assoc]

theorem const_toUnit (X : C) (x : 𝟙_ C ⟶ X) : const X x = toUnit ≫ x := by
  dsimp [const, toUnit]
  simp only [assoc, Iso.cancel_iso_inv_left]
  apply Eq.symm
  apply prec_uniq
  · rw [← assoc]; rw [zero_iter]
  · rw [← assoc]; rw [succ_iter]; simp only [comp_id]

open bool coprod

variable (C)

/-- Decides if a natural number is zero or not, if zero returns `bool.false` else it returns `bool.true`. -/
noncomputable
def toBool [HasBinaryCoproducts C] : (N : C) ⟶ 𝟮 := (ρ_ _).inv ≫ prec inl constTrue

theorem toBool_desc_eq_toUnit [HasBinaryCoproducts C] : toBool C ≫ bool.toUnit = NNO.toUnit := by
  refine (Iso.eq_inv_comp (ρ_ N)).mpr ?_
  rw [iter]
  apply prec_uniq
  · dsimp [toBool]
    have : zero ▷ 𝟙_ C ≫ (ρ_ N).hom ≫ ((ρ_ N).inv ≫ prec inl constTrue) ≫ bool.toUnit =
    (zero ▷ 𝟙_ C ≫ ((ρ_ N).hom ≫ (ρ_ N).inv) ≫ prec inl constTrue) ≫ bool.toUnit := by {
      simp only [whiskerRight_id, assoc, Iso.hom_inv_id_assoc]
    }
    rw [this]; clear this
    simp only [ Iso.hom_inv_id, id_comp, comp_id]
    rw [zero_prec]
    rw [unitors_equal, bool.toUnit, elim]
    simp only [assoc, colimit.ι_desc, BinaryCofan.mk_pt,
     BinaryCofan.ι_app_left, BinaryCofan.mk_inl, comp_id]
  · simp only [whiskerRight_id, assoc, comp_id]
    have : (ρ_ N).hom ≫ succ ≫ (ρ_ N).inv ≫ (ρ_ N).hom ≫ toBool C ≫ bool.toUnit =
    (((ρ_ N).hom ≫ succ) ≫ (ρ_ N).inv) ≫ (((ρ_ N).hom) ≫ toBool C ≫ bool.toUnit) := by {
      simp only [assoc, Iso.inv_hom_id_assoc]}
    rw [this]; clear this
    rw [rightUnitor_inv_naturality]
    simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
    rw [← assoc]
    dsimp [toBool]
    rw [← assoc]
    rw [rightUnitor_inv_naturality]
    rw [assoc, assoc]
    have : (ρ_ N).inv ≫ succ ▷ 𝟙_ C ≫ prec inl constTrue ≫ bool.toUnit=
    (ρ_ N).inv ≫ (succ ▷ 𝟙_ C ≫ prec inl constTrue) ≫ bool.toUnit := by {
      simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc]}
    rw [this]; clear this
    simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
    rw [← assoc,rightUnitor_inv_naturality]
    rw [assoc]
    refine _ ≫= ?_
    rw [← assoc,succ_prec]
    rw [assoc]
    refine _ ≫= ?_
    rw [constTrue_eq_toUnit_true]
    dsimp [bool.toUnit,elim,bool.true]
    simp only [desc_comp, id_comp, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.ι_app_right,
      BinaryCofan.mk_inr]

/-- Converts a boolean value to a natural number, sending `bool.false` to `0` and `bool.true` to `1`. -/
noncomputable def fromBool [HasBinaryCoproducts C] : 𝟮 ⟶ (N : C) := bool.elim zero one

variable {C}

theorem zero_toBool [HasBinaryCoproducts C] :
    zero ≫ toBool C = bool.false := by
  dsimp [toBool]
  rw [← assoc, rightUnitor_inv_naturality]
  rw [assoc, zero_prec]
  dsimp [bool.false]
  refine (Iso.inv_comp_eq (ρ_ (𝟙_ C))).mpr ?_
  refine ?_ =≫ _
  exact unitors_equal

theorem succ_toBool [HasBinaryCoproducts C] :
    succ ≫ toBool C = toUnit ≫ bool.true := by
  rw [← toBool_desc_eq_toUnit]
  unfold toBool
  rw [← assoc, rightUnitor_inv_naturality, assoc, assoc, assoc]
  refine _ ≫= ?_
  rw [← assoc]
  rw [succ_prec, assoc]
  refine _ ≫= ?_
  exact constTrue_eq_toUnit_true

theorem false_fromBool [HasBinaryCoproducts C] :
    bool.false ≫ fromBool C = zero := by
  simp only [fromBool, false_elim]

theorem true_fromBool [HasBinaryCoproducts C] :
    bool.true ≫ fromBool C = one := by
  simp only [fromBool, true_elim]

theorem fromBool_toBool [HasBinaryCoproducts C] :
    fromBool C ≫ toBool C = 𝟙 (𝟮 : C) := by
  apply bool.ext
  · simp only [← assoc, false_fromBool, zero_toBool, comp_id]
  · simp only [← assoc, true_fromBool, one]
    rw [assoc]
    simp only [succ_toBool, comp_id, ← assoc, zero_toUnit, id_comp]

section Comon

variable [MonoidalCategory C] [NNO C]

/-- Duplicates a natural number, it maps `n` to `n ⊗ n`. Note that this is not necessarily the diagonal morphism, it
does not use the cartesian monoidal structure. -/
def duplicate : (N : C) ⟶ N ⊗ N :=
  (ρ_ _).inv ≫ prec ((λ_ _).inv ≫ (zero ⊗ₘ zero)) (succ ⊗ₘ succ)

abbrev delete : N ⟶ 𝟙_ C := toUnit

/-- The comonoid structure on the natural number object. -/
instance comonClass : Comon_Class (N : C) where
  counit := delete
  comul := duplicate
  counit_comul := by
    simp only [duplicate, delete]
    rw [assoc]
    dsimp [toUnit]
    sorry
  comul_counit := sorry
  comul_assoc := sorry

variable (P)

/-- The type of twists maps of monoidal powers of `N`. -/
def Twist : ℕ → Type v := fun k => (N^[k] ⊗ P ⟶ P ⊗ N^[k])

def twist₀ : Twist P 0 := (λ_ P).hom ≫ (ρ_ P).inv

/-- The twist map induced by the universal property of the natural number object. -/
def twist₁ : Twist P 1 := prec ((ρ_ _ ).inv ≫ (P ◁ zero)) (P ◁ succ)

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

theorem twist₁_braiding [BraidedCategory C] {P : C} :
    twist₁ P = (β_ N P).hom := by
  dsimp [twist₁, prec]
  rw [← prec_uniq]
  · simp only [BraidedCategory.braiding_naturality_left,
      braiding_tensorUnit_left, assoc]
  · simp only [BraidedCategory.braiding_naturality_left]

theorem twist₁_is_iso {P : C} [BraidedCategory C] : IsIso (twist₁ P) := by
  rw [twist₁_braiding]
  infer_instance

theorem twist₁_twist₁ : twist₁ N ≫ twist₁ N = 𝟙 (N ⊗ N : C) := by
  sorry

def twist : (k : ℕ) → Twist P k
  | 0 => twist₀ P
  | n + 1 => (powSuccIso N n).hom ▷ P ≫ (α_ N _ P).hom ≫ (N ◁ twist n) ≫ (α_ _ _ _).inv ≫
   (twist₁ P ▷ N^[n]) ≫ (α_ _ _ _).hom ≫ (P ◁ (powSuccIso N n).inv)

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
  simp only [one, add, iter, one ]
  rw [tensorHom_def, assoc, prec_precompose]
  refine (Iso.inv_comp_eq (λ_ (𝟙_ C))).mp ?_
  rw [comp_whiskerRight, assoc, succ_prec]
  have : (λ_ (𝟙_ C)).inv ≫ zero ▷ 𝟙_ C ≫ prec (zero ≫ 𝟙 N) succ ≫ succ=
  (λ_ (𝟙_ C)).inv ≫ (zero ▷ 𝟙_ C ≫ prec (zero ≫ 𝟙 N) succ) ≫ succ := by {
    simp only [whiskerRight_id, comp_id, assoc]}
  rw [this]
  clear this
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

def iterCurried {P : C} [Closed P] [BraidedCategory C] (f : P ⟶ P) : N ⟶ (P ⟶[C] P) :=
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

/-- In a list-arithmetic category, the natural number object is isomorphic to the list object
on the unit. -/
def listUnitIsoNNO [MonoidalCategory C] [ListArithmetic C] : list (𝟙_ C) ≅ N := Iso.refl _

namespace list

open Limits

variable {C} [SemiCartesianMonoidalCategory C] [ListArithmetic C]

/-- The length of a list. -/
def len {A : C} : list A ⟶ N :=
  list.map <| SemiCartesianMonoidalCategory.toUnit A

section length

open SemiCartesianMonoidalCategory

variable {A : C}

theorem len_eq_rec_zero_snd_succ {A : C} :
    list.len (A:= A) = list.rec zero (snd A N ≫ succ) := by
  sorry

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
  rw [list.cons_map]
  rw [← Category.assoc]
  rw [tensorHom_def']
  congr 1
  simp_all only [Iso.hom_inv_id_assoc]

theorem append_len_add : list.append (A:= A) ≫ list.len = (list.len ⊗ₘ list.len) ≫ add := by
  sorry

set_option diagnostics true in
-- len ([x]) = 1
theorem singleton_len_one :
    list.singleton ≫ list.len = toUnit A ≫ one := by
  dsimp [len, singleton, one]
  sorry

/-- Promoting the length morphism to an internal monoid homomorphism from `list A` to `N`. -/
def list.lenMonHom [BraidedCategory C] {A : C} :
    Mon_.mk (list A) ⟶ Mon_.mk N :=
  Mon_.Hom.mk' (list.len (A:= A)) list.nil_len_zero list.append_len_add

end length

end list

namespace NNO

section const

variable {C} [SemiCartesianMonoidalCategory C] [NNO C]

open SemiCartesianMonoidalCategory

/-- `∀ n, f (succ n, a) = f (n, a)` implies `∀ n, f (n, a) = f (0, a)`. -/
theorem const_of_no_change_succ {P B : C} (r : N ⊗ P ⟶ B) (no_change_succ : succ ▷ P ≫ r = r) {n} :
    r = (constMorphism N n) ▷ P ≫ r := by
  sorry

end const

end NNO

end CategoryTheory
