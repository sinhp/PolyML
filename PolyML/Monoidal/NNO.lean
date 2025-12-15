/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.Tactic.CategoryTheory.Coherence
import PolyML.Monoidal.Bool
import PolyML.ForMathlib.Monoidal.AddMon_
import PolyML.ForMathlib.Monoidal.Powers
import PolyML.Monoidal.PNNO

universe u v

namespace CategoryTheory

open Category Opposite MonoidalCategory Limits

variable {C : Type u} [Category.{v} C]

/-- Natural number object in a monoidal category. -/
class IsNNO [MonoidalCategory C] (N : C) (zero : 𝟙_ C ⟶ N) (succ : N ⟶ N) where
  rc (zero succ) {B : C} (f : 𝟙_ C ⟶ B) (g : B ⟶ B) : N ⟶ B
  zero_rc {B : C} {f : 𝟙_ C ⟶ B} {g : B ⟶ B} : zero ≫ rc f g = f
  succ_rc {B : C} {f : 𝟙_ C ⟶ B} {g : B ⟶ B} : succ ≫ rc f g = rc f g ≫ g
  rc_uniq {B : C} {f : 𝟙_ C ⟶ B} {g : B ⟶ B} (r : N ⟶ B)
    (h_zero : zero ≫ r = f) (h_succ : succ ≫ r = r ≫ g) : r = rc f g

/-- Any two natural number objects in a monoidal category are isomorphic. -/
def IsNNO.iso [MonoidalCategory C] (N N' : C) {zero : 𝟙_ C ⟶ N} {succ : N ⟶ N}
    {zero' : 𝟙_ C ⟶ N'} {succ' : N' ⟶ N'}
    [IsNNO N zero succ] [IsNNO N' zero' succ'] : N ≅ N' where
  hom := rc zero succ zero' succ'
  inv := rc zero' succ' zero succ
  hom_inv_id := by
    sorry
  inv_hom_id := by
    sorry

variable (C)

class NNO [MonoidalCategory C] where
  /-- The (left) natural number object. -/
  N : C
  /-- The zero morphism. -/
  zero : 𝟙_ C ⟶ N
  /-- The successor morphism. -/
  succ : N ⟶ N
  /-- The natural number object satisfies the properties of a left natural number object. -/
  [isNNO : IsNNO N zero succ]

attribute [instance] NNO.isNNO

variable {C}

open IsPNNO

/-- Every parameterized natural number object in a monoidal closed category is a natural number object. -/
def IsPNNO.toIsNNO [MonoidalCategory C] (N : C) (zero : 𝟙_ C ⟶ N) (succ : N ⟶ N)
    [IsPNNO N zero succ] : IsNNO N zero succ where
  rc := fun {B} f g => (ρ_ N).inv ≫ IsPNNO.prc zero succ f g
  zero_rc := by
    intros B f g
    simp only [← assoc]
    rw [rightUnitor_inv_naturality]
    simp only [assoc]
    rw [zero_prc]
    rw [unitors_equal]
    simp only [Iso.inv_hom_id_assoc]
  succ_rc := by
    intros B f g
    simp only [← assoc]
    rw [rightUnitor_inv_naturality]
    simp only [assoc]
    rw [succ_prc]
  rc_uniq := by
    intros B f g r h_zero h_succ
    refine (Iso.eq_inv_comp (ρ_ N)).mpr ?_
    apply prc_uniq
    · rw [unitors_equal]
      simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
      exact h_zero
    · simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
      exact h_succ

/- In monoidal closed categories, every natural number object is a parameterized natural number object. -/
def IsNNO.toIsPNNO [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C] (N : C) (zero : 𝟙_ C ⟶ N)
    (succ : N ⟶ N) [IsNNO N zero succ] : IsPNNO N zero succ where
  prc := fun {P B} f g => (β_ N P).hom ≫
      (MonoidalClosed.uncurry <|
        IsNNO.rc zero succ ((MonoidalClosed.curry (ρ_ P).hom) ≫ (ihom P).map f) ((ihom P).map g))
  zero_prc := by
    intros A B f g
    simp only [BraidedCategory.braiding_naturality_left_assoc, braiding_tensorUnit_left,
      Category.assoc, Iso.cancel_iso_hom_left]
    rw [← MonoidalClosed.curry_natural_right]
    rw [MonoidalClosed.uncurry_eq]
    nth_rw 2 [← assoc]
    rw [← whiskerLeft_comp A, IsNNO.zero_rc]
    simp only [MonoidalClosed.whiskerLeft_curry_ihom_ev_app, Iso.inv_hom_id_assoc]
  succ_prc := by
    intros A B f g
    simp only [BraidedCategory.braiding_naturality_left_assoc,
      Category.assoc, Iso.cancel_iso_hom_left]
    rw [← MonoidalClosed.curry_natural_right]
    rw [MonoidalClosed.uncurry_eq]
    nth_rw 1 [← assoc]
    rw [← whiskerLeft_comp A, IsNNO.succ_rc]
    simp only [whiskerLeft_comp, assoc, ihom.ev_naturality, Functor.comp_obj, curriedTensor_obj_obj,
      Functor.id_obj]
  prc_uniq := by
    intros A B f g r hz hs
    refine (Iso.inv_comp_eq (β_ N A)).mp ?_
    rw [← MonoidalClosed.curry_eq_iff]
    apply IsNNO.rc_uniq
    · simp [MonoidalClosed.curry_eq]
      refine _ ≫= ?_
      rw [← Functor.map_comp]
      rw [← Functor.map_comp]
      rw [← Functor.map_comp]
      simp only [← assoc]
      rw [BraidedCategory.braiding_inv_naturality_right]
      simp only [assoc]
      rw [hz]
      simp only [braiding_inv_tensorUnit_left, assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
    · simp [MonoidalClosed.curry_eq]
      refine _ ≫= ?_
      rw [← Functor.map_comp]
      rw [← Functor.map_comp]
      rw [← Functor.map_comp]
      rw [← Functor.map_comp]
      simp only [← assoc, BraidedCategory.braiding_inv_naturality_right]
      simp only [assoc]
      rw [hs]

open PNNO IsPNNO

@[simps]
def PNNO.toNNO [MonoidalCategory C] [PNNO C] : NNO C where
  N := N
  zero := zero
  succ := succ
  isNNO := IsPNNO.toIsNNO N zero succ

/-- Any parameterized natural number object is isomorphic to any natural number object. -/
def PNNO.isoNNO [MonoidalCategory C] [PNNO C] [NNO C]: PNNO.N (C:= C) ≅ NNO.N  :=
  @IsNNO.iso _ _ _ PNNO.N NNO.N _ _ _ _  (IsPNNO.toIsNNO N zero succ) (NNO.isNNO)

namespace NNO

open IsNNO

variable [MonoidalCategory C] [NNO C] {B : C}

abbrev rc (f : 𝟙_ C ⟶ B) (g : B ⟶ B) : N ⟶ B :=
  isNNO.rc f g

@[simp]
theorem zero_rc {f : 𝟙_ C ⟶ B} {g : B ⟶ B} :
    zero ≫ rc f g = f := by
  apply IsNNO.zero_rc

theorem succ_rc {f : 𝟙_ C ⟶ B} {g : B ⟶ B} :
    succ ≫ rc f g = rc f g ≫ g := by
  apply IsNNO.succ_rc

/-- The morphism for number one, i.e. the successor of zero. -/
def one : 𝟙_ C ⟶ N := zero ≫ succ

/-- Maps any natural number to the fixed element `x`. -/
def const (X : C) (x : 𝟙_ C ⟶ X) : N ⟶ X := rc x (𝟙 X)

def toUnit : N ⟶ 𝟙_ C := const (𝟙_ C) (𝟙 _)

@[reassoc (attr := simp)]
theorem zero_toUnit : zero ≫ toUnit = 𝟙 (𝟙_ C) := by
  simp [toUnit, const]

theorem succ_toUnit : succ ≫ toUnit = toUnit (C := C) := by
  simp [toUnit, const, succ_rc]

open bool coprod

variable (C)

/-- Decides if a natural number is zero or not, if zero returns `bool.false` else it returns `bool.true`. -/
def toBool [Bool C] : (N : C) ⟶ 𝟮_ C := rc Bool.ff Bool.ttConst

/-- Converts a boolean value to a natural number, sending `bool.false` to `0` and `bool.true` to `1`. -/
def fromBool [Bool C] : 𝟮_ C ⟶ N := Bool.elim zero one

variable {C}

theorem zero_toBool [Bool C] :
    zero ≫ toBool C = Bool.ff := by
  dsimp [toBool, Bool.ff]
  rw [zero_rc]

theorem succ_toBool [Bool C] :
    succ ≫ toBool C = toUnit ≫ Bool.tt := by
  rw [toUnit, toBool, succ_rc, const]
  sorry

@[simp]
theorem false_fromBool [Bool C] :
    Bool.ff ≫ fromBool C = zero := by
  simp only [fromBool, IsBool.ff_elim]

@[simp]
theorem true_fromBool [Bool C] :
    Bool.tt ≫ fromBool C = one := by
  simp only [fromBool, IsBool.tt_elim]

theorem fromBool_toBool [Bool C] :
    fromBool C ≫ toBool C = 𝟙 (𝟮_ C) := by
  ext
  · simp only [← assoc, false_fromBool, zero_toBool, comp_id]
  · sorry

@[simps pt]
def binaryCofanZeroSucc [MonoidalCategory C] [NNO C] : BinaryCofan (𝟙_ C) N where
  pt := N
  ι := {
    app := fun
          | ⟨.left⟩ => zero
          | ⟨.right⟩ => succ
    naturality := fun ⟨X⟩ ⟨Y⟩ ⟨⟨u⟩⟩ => by
      cases X  <;> cases Y <;> repeat (first | contradiction | aesop)
  }

/-- If `N` is an NNO then `1 + N` is also an NNO. -/
@[simps]
noncomputable def isNNOOnePlus [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N] :
    IsNNO (𝟙_ C ⨿ N) (coprod.inl) (coprod.desc zero succ ≫ coprod.inr) where
  rc {B} b g := coprod.desc b (rc (b ≫ g) g)
  zero_rc := by
    intros A f g
    simp only [colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.mk_inl]
  succ_rc := by
    intros B f g
    simp only [coprod.desc_comp, assoc, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.mk_inr]
    unfold NNO.rc
    rw [IsNNO.zero_rc]
    rw [IsNNO.succ_rc]
  rc_uniq := by
    intros B f g r hr1 hr2
    refine coprod.hom_ext_iff.mpr ?_
    · rw [hr1]
      simp only [colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.mk_inl, BinaryCofan.mk_inr,
        true_and]
      apply isNNO.rc_uniq
      · rw [← hr1]
        simp only [assoc]
        rw [← hr2]
        simp only [coprod.desc_comp, assoc, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.mk_inl]
      · rw [assoc]
        rw [← hr2]
        simp only [coprod.desc_comp, assoc, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.mk_inr]

theorem inl_isNNOOnePlus_rc [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N]
    {B : C} (b : 𝟙_ C ⟶ B) (g : B ⟶ B) :
    inl ≫ isNNOOnePlus.rc b g = b := by
  simp

theorem inr_isNNOOnePlus_rc [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N]
    {B : C} (b : 𝟙_ C ⟶ B) (g : B ⟶ B) :
    zero ≫ inr ≫ isNNOOnePlus.rc b g = b ≫ g := by
  simp

@[simp]
theorem succ_inr_isNNOOnePlus_rc [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N]
    {B : C} (b : 𝟙_ C ⟶ B) (g : B ⟶ B) :
    succ ≫ inr ≫ isNNOOnePlus.rc b g = isNNO.rc b g ≫ g ≫ g := by
  simp
  sorry

@[simp]
theorem zero_succ_inr_isNNOOnePlus_rc [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N]
    {B : C} (b : 𝟙_ C ⟶ B) (g : B ⟶ B) :
    zero ≫ succ ≫ inr ≫ isNNOOnePlus.rc b g = b ≫ g ≫ g  := by
  rw [succ_inr_isNNOOnePlus_rc]
  rw [← assoc]
  rw [IsNNO.zero_rc]

/-- `N` is isomorphic to `1 + N`. -/
noncomputable def NNOIsoOnePlus [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N] :
    NNO.N ≅ (𝟙_ C ⨿ N) :=
  @IsNNO.iso _ _ _ N (𝟙_ C ⨿ N) _ _ _ _ (NNO.isNNO) isNNOOnePlus

theorem NNOIsoOnePlus_inv [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N] :
    (NNOIsoOnePlus).inv = coprod.desc (NNO.zero : 𝟙_ C ⟶ N) NNO.succ := by
  --have := IsColimit.uniq _
  --rw [coprod.desc, colimit.desc, colimit.isColimit]
  -- rw [IsColimit.uniq]
  sorry

#check CategoryTheory.Limits.coprod.desc'

/-- The diagram `𝟙_C ⟶ N ⟵ N`  is a coproduct diagram. -/
noncomputable def colimitCocone [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N] :
  ColimitCocone (pair (𝟙_ C) N) where
    cocone := binaryCofanZeroSucc
    isColimit := by
      refine BinaryCofan.IsColimit.mk (C:= C) ?_ ?_ ?_ ?_ ?_
      · intro S a b
        exact NNOIsoOnePlus.hom ≫ (coprod.desc a b)
      · sorry
      · sorry
      · sorry

/-- The diagram `T_C ⟶ N ⟵ N` is a colimit diagram. -/
def BinaryCoproduct [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N] :
    HasBinaryCoproduct (𝟙_ C) N where
  exists_colimit := by
    constructor
    exact colimitCocone

variable (C) in
/-- The numerals as morphisms from the unit object to the NNO. -/
def num [MonoidalCategory C] [NNO C] : ℕ → (𝟙_ C ⟶ N)
  | Nat.zero => zero
  | Nat.succ m => num m ≫ succ

section Num

@[simp]
theorem num_zero : num C (0 : ℕ) = zero := by
  rfl

@[simp]
theorem num_succ (n : ℕ) :
    num C (n + 1) = num C n ≫ succ := by
  rfl

@[simp]
theorem num_one : num C (1 : ℕ) = one := by
  rw [num_succ, num_zero, one]

def num_pair (m n : ℕ) : (𝟙_ C ⟶ N ⊗ N) :=
  (ρ_ _).inv ≫ (num C m ⊗ₘ num C n)

end Num

end NNO

end CategoryTheory
