/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Monoidal.Comon_
import PolyML.Monoidal.ListArithmetic
import PolyML.ForMathlib.Monoidal.Powers
import Mathlib.Tactic.CategoryTheory.Coherence
import PolyML.ForMathlib.Bool
import Mathlib.CategoryTheory.Closed.Cartesian

universe u v

namespace CategoryTheory

open Category Opposite MonoidalCategory Limits

-- attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

variable {C : Type u} [Category.{v} C]

-- SH: prc for "parameterized" rcursion.
-- SH: usually params are on the left, although this becomes incompatible with plist.
/-- Parameterized natural number object in a monoidal category. -/
class IsPNNO [MonoidalCategory C] (N : C) (zero : 𝟙_ C ⟶ N) (succ : N ⟶ N) where
  prc (zero succ) {P B : C} (f : P ⟶ B) (g : B ⟶ B) : N ⊗ P ⟶ B
  zero_prc {P B : C} {f : P ⟶ B} {g : B ⟶ B} : (zero ▷ P) ≫ prc f g = (λ_ P).hom ≫ f
  succ_prc {P B : C} {f : P ⟶ B} {g : B ⟶ B} : (succ ▷ P) ≫ prc f g = prc f g ≫ g
  prc_uniq {P B : C} {f : P ⟶ B} {g : B ⟶ B} (r : N ⊗ P ⟶ B)
  (h_zero : (zero ▷ P) ≫ r = (λ_ P).hom ≫ f) (h_succ: (succ ▷ P) ≫ r = r ≫ g) : r = prc f g

/-- Natural number object in a monoidal category. -/
class IsNNO [MonoidalCategory C] (N : C) (zero : 𝟙_ C ⟶ N) (succ : N ⟶ N) where
  rc (zero succ) {B : C} (f : 𝟙_ C ⟶ B) (g : B ⟶ B) : N ⟶ B
  zero_rc {B : C} {f : 𝟙_ C ⟶ B} {g : B ⟶ B} : zero ≫ rc f g = f
  succ_rc {B : C} {f : 𝟙_ C ⟶ B} {g : B ⟶ B} : succ ≫ rc f g = rc f g ≫ g
  rc_uniq {B : C} {f : 𝟙_ C ⟶ B} {g : B ⟶ B} (r : N ⟶ B)
    (h_zero : zero ≫ r = f) (h_succ : succ ≫ r = r ≫ g) : r = rc f g

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
(succ : N ⟶ N)
    [IsNNO N zero succ] : IsPNNO N zero succ where
  prc := fun {P B} f g => (β_ N P).hom ≫
      (MonoidalClosed.uncurry <| rc zero succ ((MonoidalClosed.curry (ρ_ P).hom) ≫ (ihom P).map f) ((ihom P).map g))
  zero_prc := by
    intros A B f g
    simp only [BraidedCategory.braiding_naturality_left_assoc, braiding_tensorUnit_left,
      Category.assoc, Iso.cancel_iso_hom_left]
    rw [← MonoidalClosed.curry_natural_right]
    rw [MonoidalClosed.uncurry_eq]
    nth_rw 2 [← assoc]
    rw [← whiskerLeft_comp A, zero_rc]
    simp only [MonoidalClosed.whiskerLeft_curry_ihom_ev_app, Iso.inv_hom_id_assoc]
  succ_prc := by
    intros A B f g
    simp only [BraidedCategory.braiding_naturality_left_assoc,
      Category.assoc, Iso.cancel_iso_hom_left]
    rw [← MonoidalClosed.curry_natural_right]
    rw [MonoidalClosed.uncurry_eq]
    nth_rw 1 [← assoc]
    rw [← whiskerLeft_comp A, succ_rc]
    simp only [whiskerLeft_comp, assoc, ihom.ev_naturality, Functor.comp_obj, curriedTensor_obj_obj,
      Functor.id_obj]
  prc_uniq := by
    intros A B f g r hz hs
    refine (Iso.inv_comp_eq (β_ N A)).mp ?_
    rw [← MonoidalClosed.curry_eq_iff]
    apply rc_uniq
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

namespace IsPNNO

variable [MonoidalCategory C]

variable {N : C} {zero : 𝟙_ C ⟶ N} {succ : N ⟶ N} [IsPNNO N zero succ]

theorem congr_arg {P B : C} {f f' : P ⟶ B} {g g' : B ⟶ B}
    (h : f = f') (h' : g = g') :
    prc zero succ f g = prc zero succ f' g' := by
  subst h h'
  rfl

/-- Any two natural number objects in a monoidal category are isomorphic. -/
def iso {N N' : C} {zero : 𝟙_ C ⟶ N} {succ : N ⟶ N} {zero' : 𝟙_ C ⟶ N'} {succ' : N' ⟶ N'}
    [IsPNNO N zero succ] [IsPNNO N' zero' succ'] : N ≅ N' where
  hom := (ρ_ N).inv ≫ prc zero succ zero' succ'
  inv := (ρ_ N').inv ≫ prc zero' succ' zero succ
  hom_inv_id := by stop
    simp only [Category.assoc]

    have h : prc zero succ zero' succ' ≫ (ρ_ N').inv ≫ prc zero' succ' zero succ =
             prc zero succ zero succ := by
      apply IsPNNO.prc_uniq (zero := zero) (succ := succ)

      · -- BASE CASE (h_zero)
        rw [← Category.assoc]
        rw [IsPNNO.zero_prc]

        -- THE FIX: Flatten the parentheses so we don't grab `λ.hom`!
        simp only [Category.assoc]

        -- Isolate ONLY `zero'` and apply naturality
        rw [← Category.assoc (f := zero')]
        erw [rightUnitor_inv_naturality]

        -- Flatten again
        simp only [Category.assoc]

        -- NOW `zero' ▷ 𝟙_ C` is perfectly isolated!
        rw [← Category.assoc (f := zero' ▷ 𝟙_ C)]
        rw [IsPNNO.zero_prc]

        -- Clean up unitors
        simp only [Category.assoc]
        have h_unit : (λ_ (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).inv = 𝟙 _ := by
          rw [unitors_equal, Iso.hom_inv_id]
        rw [← Category.assoc (f := (λ_ (𝟙_ C)).hom)]
        rw [h_unit]
        simp only [Category.id_comp]

      · -- INDUCTIVE CASE (h_succ)
        -- Isolate the first recursor
        rw [← Category.assoc]
        rw [IsPNNO.succ_prc]

        -- Commute succ past the unitor
        simp only [Category.assoc]
        rw [← Category.assoc (f := succ')]
        erw [rightUnitor_inv_naturality]

        -- Apply the second recursor
        simp only [Category.assoc]
        rw [← Category.assoc (f := succ' ▷ 𝟙_ C)]
        rw [IsPNNO.succ_prc]
        simp only [Category.assoc]

    -- 2. Prove that the identity recursor evaluates exactly to the right unitor
    have h_id : prc zero succ zero succ = (ρ_ N).hom := by
      apply IsPNNO.prc_uniq (zero := zero) (succ := succ)
      · coherence
      · apply rightUnitor_naturality

    -- 3. Substitute our isolated facts back into the main goal!
    rw [← Category.assoc (f := prc zero succ zero' succ')]
    rw [h]
    rw [h_id]
    exact Iso.inv_hom_id (ρ_ N)

  inv_hom_id := by stop
    dsimp [hom, inv]
    simp only [Category.assoc]

    -- We repeat the exact same symmetrical logic for the opposite direction!
    have h : prc zero' succ' zero succ ≫ (ρ_ N).inv ≫ prc zero succ zero' succ' =
             prc zero' succ' zero' succ' := by
      apply IsPNNO.prc_uniq (zero := zero') (succ := succ')
      · -- BASE CASE
        rw [← Category.assoc]
        rw [IsPNNO.zero_prc]
        rw [← Category.assoc]
        erw [rightUnitor_inv_naturality]
        simp only [Category.assoc]
        rw [← Category.assoc (f := zero ▷ 𝟙_ C)]
        rw [IsPNNO.zero_prc]
        simp only [Category.assoc]
        rw [← Category.assoc (f := (ρ_ (𝟙_ C)).inv)]
        rw [unitors_equal]
        rw [Iso.inv_hom_id_assoc]
      · -- INDUCTIVE CASE
        rw [← Category.assoc]
        rw [IsPNNO.succ_prc]
        simp only [Category.assoc]
        rw [← Category.assoc (f := succ)]
        erw [rightUnitor_inv_naturality]
        simp only [Category.assoc]
        rw [← Category.assoc (f := succ ▷ 𝟙_ C)]
        rw [IsPNNO.succ_prc]
        simp only [Category.assoc]

    have h_id : prc zero' succ' zero' succ' = (ρ_ N').hom := by
      apply IsPNNO.prc_uniq (zero := zero') (succ := succ')
      · coherence
      · apply rightUnitor_naturality

    rw [← Category.assoc (f := prc zero' succ' zero succ)]
    rw [h]
    rw [h_id]
    exact Iso.inv_hom_id (ρ_ N')

-- /-- Any two natural number objects in a monoidal category are isomorphic. -/
-- def iso {N N' : C} {zero : 𝟙_ C ⟶ N} {succ : N ⟶ N} {zero' : 𝟙_ C ⟶ N'} {succ' : N' ⟶ N'}
--     [IsPNNO N zero succ] [IsPNNO N' zero' succ'] : N ≅ N' where
--   hom := (ρ_ N).inv ≫ prc zero succ zero' succ'
--   inv := (ρ_ N').inv ≫ prc zero' succ' zero succ
--   hom_inv_id := sorry
--   inv_hom_id := sorry

end IsPNNO

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
  [isPNNO : IsPNNO N zero succ]

-- @[inherit_doc] notation "N_" => NNO.N

abbrev nno (C : Type u) [Category.{v} C] [MonoidalCategory C] [NNO C] : C := NNO.N

namespace NNO

open IsPNNO

variable {C} [MonoidalCategory C] [NNO C] {P B : C}

instance : IsPNNO N (zero : 𝟙_ C ⟶ N) (succ : N ⟶ N) :=
  NNO.isPNNO

def prc (f : P ⟶ B) (g : B ⟶ B) : N ⊗ P ⟶ B :=
  IsPNNO.prc zero succ f g

@[simp]
theorem zero_prc {f : P ⟶ B} {g : B ⟶ B} :
  (zero ▷ P) ≫ prc f g = (λ_ P).hom ≫ f := by
  apply IsPNNO.zero_prc

theorem succ_prc {f : P ⟶ B} {g : B ⟶ B} :
  (succ ▷ P) ≫ prc f g = prc f g ≫ g := by
  apply IsPNNO.succ_prc

theorem prc_prcompose {P'} {u : P' ⟶ P} {f : P ⟶ B} {g : B ⟶ B} :
  N ◁ u ≫ prc f g = prc (u ≫ f) g := by
  apply prc_uniq
  all_goals rw [← assoc, ← whisker_exchange, assoc]
  · rw [zero_prc]
    aesop
  · rw [succ_prc]
    aesop

theorem prc_postcompose {B'} {f : P ⟶ B} {g : B ⟶ B} (g' : B' ⟶ B') (d : B ⟶ B')
    (comm_sq : CommSq g d d g' := by aesop) :
    prc f g ≫ d = prc (f ≫ d) g' := by
  apply prc_uniq
  · rw [← assoc, zero_prc]
    simp only [assoc]
  · rw [← assoc, succ_prc]
    simp only [assoc]
    refine _ ≫= ?_
    exact comm_sq.w

/-- Iterates an endomorphism `n` times. -/
def iter (f : P ⟶ P) : N ⊗ P ⟶ P := prc (𝟙 _) (f)

/-- rcursion with the parameter `P` set to the unit object `𝟙_ C` -/
def urc (f : 𝟙_ C ⟶ B) (g : B ⟶ B) : N ⟶ B :=
  (ρ_ _).inv ≫ prc f g

@[reassoc (attr := simp)]
theorem zero_iter {f : P ⟶ P} :
  zero ▷ P ≫ iter f = (λ_ P).hom := by
  simp [iter]

theorem succ_iter {f : P ⟶ P} :
  succ ▷ P ≫ iter f = iter f ≫ f := by
  simp [iter, succ_prc]

/-- `prc` can be rconstructed from `iter`. -/
@[reassoc (attr := simp)]
theorem iter_prc {f : P ⟶ B} {g : B ⟶ B} : (N ◁ f) ≫ iter g = prc f g := by
  simpa using prc_prcompose (u:= f) (f:= 𝟙 B) (g:= g)

theorem eq_whisker_iter {f : P ⟶ B} {g : B ⟶ B} (r : N ⊗ P ⟶ B)
    (h_zero : (zero ▷ P) ≫ r = (λ_ P).hom ≫ f) (h_succ : (succ ▷ P) ≫ r = r ≫ g) :
    r = (N ◁ f) ≫ iter g := by
  rw [iter_prc]
  apply prc_uniq
  all_goals
  assumption

-- SH : rfpi coherence
lemma prc_zero_succ_eq_rightUnitor : prc (P := 𝟙_ C) (B := N) zero succ = (ρ_ N).hom := by
  symm
  apply prc_uniq
  · coherence
  · apply rightUnitor_naturality succ

/-- The morphism for number one, i.e. the successor of zero. -/
def one : 𝟙_ C ⟶ N := zero ≫ succ

/-- Maps any natural number to the fixed element `x`. -/
def const (X : C) (x : 𝟙_ C ⟶ X) : N ⟶ X := (ρ_ _).inv ≫ prc x (𝟙 X)

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
  simp [iter, prc]
  symm
  apply prc_uniq
  · rw [← assoc, ← comp_whiskerRight, zero_toUnit, id_whiskerRight, id_comp, comp_id]
  · rw [← assoc, ← comp_whiskerRight, succ_toUnit, comp_id]

theorem iter_id_unit : iter (𝟙 (𝟙_ C)) = (ρ_ _).hom ≫ toUnit := by
  simp only [toUnit, Iso.hom_inv_id_assoc]

theorem const_toUnit (X : C) (x : 𝟙_ C ⟶ X) : const X x = toUnit ≫ x := by
  dsimp [const, toUnit]
  simp only [assoc, Iso.cancel_iso_inv_left]
  apply Eq.symm
  apply prc_uniq
  · rw [← assoc]; rw [zero_iter]
  · rw [← assoc]; rw [succ_iter]; simp only [comp_id]

open bool coprod

variable (C)

/-- Decides if a natural number is zero or not, if zero returns `bool.false` else it returns `bool.true`. -/
noncomputable
def toBool [HasBinaryCoproducts C] : (N : C) ⟶ 𝟮 := (ρ_ _).inv ≫ prc inl constTrue

theorem toBool_desc_eq_toUnit [HasBinaryCoproducts C] : toBool C ≫ bool.toUnit = NNO.toUnit := by
  refine (Iso.eq_inv_comp (ρ_ N)).mpr ?_
  rw [iter]
  apply prc_uniq
  · dsimp [toBool]
    have : zero ▷ 𝟙_ C ≫ (ρ_ N).hom ≫ ((ρ_ N).inv ≫ prc inl constTrue) ≫ bool.toUnit =
    (zero ▷ 𝟙_ C ≫ ((ρ_ N).hom ≫ (ρ_ N).inv) ≫ prc inl constTrue) ≫ bool.toUnit := by
      simp only [whiskerRight_id, assoc, Iso.hom_inv_id_assoc]
    rw [this]; clear this
    simp only [ Iso.hom_inv_id, id_comp, comp_id]
    rw [zero_prc]
    rw [unitors_equal, bool.toUnit, elim]
    simp only [assoc, colimit.ι_desc, BinaryCofan.mk_pt,
     BinaryCofan.ι_app_left, BinaryCofan.mk_inl, comp_id]
  · simp only [whiskerRight_id, assoc, comp_id]
    have : (ρ_ N).hom ≫ succ ≫ (ρ_ N).inv ≫ (ρ_ N).hom ≫ toBool C ≫ bool.toUnit =
    (((ρ_ N).hom ≫ succ) ≫ (ρ_ N).inv) ≫ (((ρ_ N).hom) ≫ toBool C ≫ bool.toUnit) := by
      simp only [assoc, Iso.inv_hom_id_assoc]
    rw [this]; clear this
    rw [rightUnitor_inv_naturality]
    simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
    rw [← assoc]
    dsimp [toBool]
    rw [← assoc]
    rw [rightUnitor_inv_naturality]
    rw [assoc, assoc]
    have : (ρ_ N).inv ≫ succ ▷ 𝟙_ C ≫ prc inl constTrue ≫ bool.toUnit=
    (ρ_ N).inv ≫ (succ ▷ 𝟙_ C ≫ prc inl constTrue) ≫ bool.toUnit := by
      simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
    rw [this]; clear this
    simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
    rw [← assoc,rightUnitor_inv_naturality]
    rw [assoc]
    refine _ ≫= ?_
    rw [← assoc,succ_prc]
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
  rw [assoc, zero_prc]
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
  rw [succ_prc, assoc]
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

/-- Duplicates a natural number, it maps `n` to `n ⊗ n`. Note that this is not necessarily the diagonal morphism, it
does not use the cartesian monoidal structure. -/
def duplicate : (N : C) ⟶ N ⊗ N :=
  (ρ_ _).inv ≫ prc ((λ_ _).inv ≫ (zero ⊗ₘ zero)) (succ ⊗ₘ succ)

abbrev delete : N ⟶ 𝟙_ C := toUnit

/-- The comonoid structure on the natural number object. -/
instance comonClass : ComonObj (N : C) where
  counit := delete
  comul := duplicate
  counit_comul := by
    dsimp [duplicate, delete]
    rw [Category.assoc]

    have comm_sq : CommSq (succ ⊗ₘ succ) (toUnit ▷ N) (toUnit ▷ N) (𝟙_ C ◁ succ) := ⟨by
      rw [tensorHom_def']
      simp only [Category.assoc]
      rw [← comp_whiskerRight, succ_toUnit]
      apply whisker_exchange
    ⟩

    rw [prc_postcompose (𝟙_ C ◁ succ) (toUnit ▷ N) comm_sq]

    have h_init : ((λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ zero)) ≫ toUnit ▷ N = zero ≫ (λ_ N).inv := by
      rw [Category.assoc, tensorHom_def']
      simp only [Category.assoc, ← comp_whiskerRight, zero_toUnit, id_whiskerRight, Category.comp_id]
      rw [← leftUnitor_inv_naturality]

    rw [h_init]

    have h_id : prc (zero ≫ (λ_ N).inv) (𝟙_ C ◁ succ) = (ρ_ N).hom ≫ (λ_ N).inv := by
      apply Eq.symm
      apply prc_uniq
      · -- BASE CASE
        rw [← Category.assoc]
        -- NO LEFT ARROW HERE!
        rw [rightUnitor_naturality]
        rw [Category.assoc]
        have h_unit : (ρ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom := by rw [unitors_equal]
        rw [h_unit]

      · -- INDUCTIVE CASE
        rw [← Category.assoc]
        -- NO LEFT ARROW HERE!
        rw [rightUnitor_naturality]
        rw [Category.assoc]

        -- Safely commute succ past the unitor inverse using a calc block
        have h_left : succ ≫ (λ_ N).inv = (λ_ N).inv ≫ 𝟙_ C ◁ succ := by
          calc succ ≫ (λ_ N).inv
            _ = 𝟙 _ ≫ succ ≫ (λ_ N).inv := by rw [Category.id_comp]
            _ = ((λ_ N).inv ≫ (λ_ N).hom) ≫ succ ≫ (λ_ N).inv := by rw [Iso.inv_hom_id]
            _ = (λ_ N).inv ≫ ((λ_ N).hom ≫ succ) ≫ (λ_ N).inv := by simp only [Category.assoc]
            _ = (λ_ N).inv ≫ (𝟙_ C ◁ succ ≫ (λ_ N).hom) ≫ (λ_ N).inv := by rw [leftUnitor_naturality]
            _ = (λ_ N).inv ≫ 𝟙_ C ◁ succ ≫ ((λ_ N).hom ≫ (λ_ N).inv) := by simp only [Category.assoc]
            _ = (λ_ N).inv ≫ 𝟙_ C ◁ succ ≫ 𝟙 _ := by rw [Iso.hom_inv_id]
            _ = (λ_ N).inv ≫ 𝟙_ C ◁ succ := by rw [Category.comp_id]

        rw [h_left]
        simp

    rw [h_id, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  comul_counit := by
    dsimp [duplicate, delete]
    rw [Category.assoc]

    -- 1. Build the commutative square using a watertight calc block
    -- 1. Build the commutative square using a watertight calc block
    have comm_sq : CommSq (succ ⊗ₘ succ) (N ◁ toUnit) (N ◁ toUnit) (succ ▷ 𝟙_ C) := ⟨by
      calc (succ ⊗ₘ succ) ≫ N ◁ toUnit
        -- FIX: Added the prime (') to tensorHom_def
        _ = (N ◁ succ ≫ succ ▷ N) ≫ N ◁ toUnit := by rw [tensorHom_def']
        _ = N ◁ succ ≫ (succ ▷ N ≫ N ◁ toUnit) := by rw [Category.assoc]
        _ = N ◁ succ ≫ (N ◁ toUnit ≫ succ ▷ 𝟙_ C) := by rw [← whisker_exchange]
        _ = (N ◁ succ ≫ N ◁ toUnit) ≫ succ ▷ 𝟙_ C := by rw [← Category.assoc]
        _ = N ◁ (succ ≫ toUnit) ≫ succ ▷ 𝟙_ C := by rw [← whiskerLeft_comp]
        _ = N ◁ toUnit ≫ succ ▷ 𝟙_ C := by rw [succ_toUnit]
    ⟩

    rw [prc_postcompose (succ ▷ 𝟙_ C) (N ◁ toUnit) comm_sq]

    -- 2. Calculate the initialization case with total precision
    have h_init : ((λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ zero)) ≫ N ◁ toUnit = (λ_ (𝟙_ C)).inv ≫ zero ▷ 𝟙_ C := by
      calc ((λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ zero)) ≫ N ◁ toUnit
        _ = (λ_ (𝟙_ C)).inv ≫ ((zero ⊗ₘ zero) ≫ N ◁ toUnit) := by rw [Category.assoc]
        _ = (λ_ (𝟙_ C)).inv ≫ ((𝟙_ C ◁ zero ≫ zero ▷ N) ≫ N ◁ toUnit) := by rw [tensorHom_def']
        _ = (λ_ (𝟙_ C)).inv ≫ (𝟙_ C ◁ zero ≫ (zero ▷ N ≫ N ◁ toUnit)) := by rw [Category.assoc]
        -- FIX: The exchanged whisker is 𝟙_ C ◁ toUnit, not N ◁ toUnit!
        _ = (λ_ (𝟙_ C)).inv ≫ (𝟙_ C ◁ zero ≫ (𝟙_ C ◁ toUnit ≫ zero ▷ 𝟙_ C)) := by rw [← whisker_exchange]
        _ = (λ_ (𝟙_ C)).inv ≫ ((𝟙_ C ◁ zero ≫ 𝟙_ C ◁ toUnit) ≫ zero ▷ 𝟙_ C) := by rw [← Category.assoc];aesop
        _ = (λ_ (𝟙_ C)).inv ≫ (𝟙_ C ◁ (zero ≫ toUnit) ≫ zero ▷ 𝟙_ C) := by rw [← whiskerLeft_comp]
        _ = (λ_ (𝟙_ C)).inv ≫ (𝟙_ C ◁ 𝟙 (𝟙_ C) ≫ zero ▷ 𝟙_ C) := by rw [zero_toUnit]
        _ = (λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C ⊗ 𝟙_ C) ≫ zero ▷ 𝟙_ C) := by rw [whiskerLeft_id]
        _ = (λ_ (𝟙_ C)).inv ≫ zero ▷ 𝟙_ C := by rw [Category.id_comp]

    rw [h_init]

    -- 3. Prove the identity recursor evaluates correctly (again, zero guesswork!)
    have h_id : prc ((λ_ (𝟙_ C)).inv ≫ zero ▷ 𝟙_ C) (succ ▷ 𝟙_ C) = 𝟙 (N ⊗ 𝟙_ C) := by
      apply Eq.symm
      apply prc_uniq
      · calc zero ▷ 𝟙_ C ≫ 𝟙 (N ⊗ 𝟙_ C)
          _ = zero ▷ 𝟙_ C := by rw [Category.comp_id]
          _ = 𝟙 _ ≫ zero ▷ 𝟙_ C := by rw [Category.id_comp]
          _ = ((λ_ (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).inv) ≫ zero ▷ 𝟙_ C := by rw [Iso.hom_inv_id]
          _ = (λ_ (𝟙_ C)).hom ≫ ((λ_ (𝟙_ C)).inv ≫ zero ▷ 𝟙_ C) := by rw [Category.assoc]
      · calc succ ▷ 𝟙_ C ≫ 𝟙 (N ⊗ 𝟙_ C)
          _ = succ ▷ 𝟙_ C := by rw [Category.comp_id]
          _ = 𝟙 (N ⊗ 𝟙_ C) ≫ succ ▷ 𝟙_ C := by rw [Category.id_comp]

    rw [h_id]

    -- 4. Finish off the (ρ_ N).inv ≫ 𝟙 = (ρ_ N).inv goal
    rw [Category.comp_id]
  comul_assoc := by
    -- 1. Establish the base recursive properties of the duplicator
    -- FIX: Explicitly type `zero` and `succ` so Lean knows exactly which NNO we mean!
    have zero_duplicate : (zero : 𝟙_ C ⟶ N) ≫ duplicate = (λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ zero) := by
      dsimp [duplicate]
      rw [← Category.assoc, rightUnitor_inv_naturality, Category.assoc, zero_prc]
      have h_unit : (ρ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom = 𝟙 _ := by
        rw [unitors_equal, Iso.inv_hom_id]
      rw [← Category.assoc, h_unit, Category.id_comp]

    have succ_duplicate : (succ (C:=C) : N ⟶ N) ≫ duplicate = duplicate ≫ (succ ⊗ₘ succ) := by
      dsimp [duplicate]
      rw [← Category.assoc, rightUnitor_inv_naturality, Category.assoc, succ_prc]
      simp only [Category.assoc]

    -- 2. Convert standard whiskers into explicit tensor products to avoid definition mismatches
    have h_whisker_R : duplicate ▷ N (C:=C)= duplicate ⊗ₘ 𝟙 N := by
      rw [tensorHom_def]
      simp only [whiskerLeft_id, Category.comp_id]

    have h_whisker_L : N (C:=C) ◁ duplicate = 𝟙 N ⊗ₘ duplicate := by
      rw [tensorHom_def]
      simp only [id_whiskerRight, Category.id_comp]

    rw [h_whisker_R, h_whisker_L]

    have h_whisker_L : N (C:=C) ◁ duplicate = 𝟙 N ⊗ₘ duplicate := by
      rw [tensorHom_def]
      simp only [id_whiskerRight, Category.id_comp]

    rw [← h_whisker_R, ← h_whisker_L]

    -- 3. Isolate the recursor from the duplicator
    have hom_dup : (ρ_ N).hom ≫ duplicate = prc ((λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ zero)) (succ ⊗ₘ succ) := by
      dsimp [duplicate]
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

    -- 4. Left side inductive step commutative square
    -- 4. Left side inductive step commutative square
    -- 4. Left side inductive step commutative square
    have comm_sq_L : CommSq (succ ⊗ₘ succ) ((duplicate ⊗ₘ 𝟙 N) ≫
        (α_ N N N).hom) ((duplicate ⊗ₘ 𝟙 N) ≫ (α_ N N N).hom) (succ ⊗ₘ (succ ⊗ₘ succ)) := ⟨by
      calc (succ ⊗ₘ succ) ≫ (duplicate ⊗ₘ 𝟙 N) ≫ (α_ N N N).hom
        _ = ((succ ⊗ₘ succ) ≫ (duplicate ⊗ₘ 𝟙 N)) ≫ (α_ N N N).hom := by simp
        -- FIX: Remove the left arrow to expand!
        _ = (((succ : N ⟶ N) ≫ duplicate) ⊗ₘ ((succ : N ⟶ N) ≫ 𝟙 N)) ≫ (α_ N N N).hom := by
          rw [CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom (C:=C)]
        _ = (((succ : N ⟶ N) ≫ duplicate) ⊗ₘ (succ : N ⟶ N)) ≫ (α_ N N N).hom := by simp only [Category.comp_id]
        _ = ((duplicate ≫ (succ ⊗ₘ succ)) ⊗ₘ (succ : N ⟶ N)) ≫ (α_ N N N).hom := by rw [succ_duplicate]
        _ = ((duplicate ≫ (succ ⊗ₘ succ)) ⊗ₘ (𝟙 N ≫ succ)) ≫ (α_ N N N).hom := by simp only [Category.id_comp]
        -- Keep the left arrow here to contract it back together!
        _ = ((duplicate ⊗ₘ 𝟙 N) ≫ ((succ ⊗ₘ succ) ⊗ₘ succ)) ≫ (α_ N N N).hom := by
            rw [← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom]
        _ = (duplicate ⊗ₘ 𝟙 N) ≫ ((succ ⊗ₘ succ) ⊗ₘ succ) ≫ (α_ N N N).hom := by rw [Category.assoc]
        _ = (duplicate ⊗ₘ 𝟙 N) ≫ (α_ N N N).hom ≫ (succ ⊗ₘ (succ ⊗ₘ succ)) := by
            erw [CategoryTheory.MonoidalCategory.associator_naturality]
        _ = ((duplicate ⊗ₘ 𝟙 N) ≫ (α_ N N N).hom) ≫ (succ ⊗ₘ (succ ⊗ₘ succ)) := by rw [← Category.assoc]
    ⟩

    -- 5. Right side inductive step commutative square
    have comm_sq_R : CommSq (succ ⊗ₘ succ) (𝟙 N ⊗ₘ duplicate) (𝟙 N ⊗ₘ duplicate) (succ ⊗ₘ (succ ⊗ₘ succ)) := ⟨by
      calc (succ ⊗ₘ succ) ≫ (𝟙 N ⊗ₘ duplicate)
        _ = ((succ : N ⟶ N) ≫ 𝟙 N) ⊗ₘ ((succ : N ⟶ N) ≫ duplicate) := by
          rw [← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom (C:=C)]
        _ = (succ : N ⟶ N) ⊗ₘ ((succ : N ⟶ N) ≫ duplicate) := by simp only [Category.comp_id]
        _ = (succ : N ⟶ N) ⊗ₘ (duplicate ≫ (succ ⊗ₘ succ)) := by rw [succ_duplicate]
        _ = (𝟙 N ≫ succ) ⊗ₘ (duplicate ≫ (succ ⊗ₘ succ)) := by simp only [Category.id_comp]
        _ = (𝟙 N ⊗ₘ duplicate) ≫ (succ ⊗ₘ (succ ⊗ₘ succ)) := by
          rw [CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom]
    ⟩

    -- 6. Initialization step identity trace (The core associativity magic)
    have h_init : ((λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ zero)) ≫ (duplicate ⊗ₘ 𝟙 N) ≫
      (α_ N N N).hom = ((λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ zero)) ≫ (𝟙 N ⊗ₘ duplicate) := by
      have h_coh : ((λ_ (𝟙_ C)).inv ⊗ₘ 𝟙 (𝟙_ C)) ≫
           (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom = 𝟙 (𝟙_ C) ⊗ₘ (λ_ (𝟙_ C)).inv := by coherence
      calc ((λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ zero)) ≫ (duplicate ⊗ₘ 𝟙 N) ≫ (α_ N N N).hom
        _ = (λ_ (𝟙_ C)).inv ≫ ((zero ⊗ₘ zero) ≫ (duplicate ⊗ₘ 𝟙 N)) ≫
            (α_ N N N).hom := by simp only [Category.assoc]
        _ = (λ_ (𝟙_ C)).inv ≫ (((zero : 𝟙_ C ⟶ N) ≫ duplicate) ⊗ₘ
            ((zero : 𝟙_ C ⟶ N) ≫ 𝟙 N)) ≫ (α_ N N N).hom := by
            rw [← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom]
        _ = (λ_ (𝟙_ C)).inv ≫ (((zero : 𝟙_ C ⟶ N) ≫ duplicate) ⊗ₘ
            (zero : 𝟙_ C ⟶ N)) ≫ (α_ N N N).hom := by simp only [Category.comp_id]
        _ = (λ_ (𝟙_ C)).inv ≫ (((λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ zero)) ⊗ₘ
            (zero : 𝟙_ C ⟶ N)) ≫ (α_ N N N).hom := by simp only [zero_duplicate]
        _ = (λ_ (𝟙_ C)).inv ≫ (((λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ zero)) ⊗ₘ
            (𝟙 (𝟙_ C) ≫ (zero : 𝟙_ C ⟶ N))) ≫ (α_ N N N).hom := by simp only [Category.id_comp]
        _ = (λ_ (𝟙_ C)).inv ≫ (((λ_ (𝟙_ C)).inv ⊗ₘ 𝟙 (𝟙_ C)) ≫
            ((zero ⊗ₘ zero) ⊗ₘ (zero : 𝟙_ C ⟶ N))) ≫ (α_ N N N).hom := by
            rw [← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom]
        _ = (λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ⊗ₘ 𝟙 (𝟙_ C)) ≫ ((zero ⊗ₘ zero) ⊗ₘ (zero : 𝟙_ C ⟶ N)) ≫
            (α_ N N N).hom := by simp only [Category.assoc]
        _ = (λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ⊗ₘ 𝟙 (𝟙_ C)) ≫ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ≫
            ((zero : 𝟙_ C ⟶ N) ⊗ₘ (zero ⊗ₘ zero)) := by
            erw [CategoryTheory.MonoidalCategory.associator_naturality]
        _ = (λ_ (𝟙_ C)).inv ≫ (((λ_ (𝟙_ C)).inv ⊗ₘ 𝟙 (𝟙_ C)) ≫ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom) ≫
            ((zero : 𝟙_ C ⟶ N) ⊗ₘ (zero ⊗ₘ zero)) := by simp only [Category.assoc]
        _ = (λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ (λ_ (𝟙_ C)).inv) ≫
            ((zero : 𝟙_ C ⟶ N) ⊗ₘ (zero ⊗ₘ zero)) := by rw [h_coh]
        _ = (λ_ (𝟙_ C)).inv ≫ ((𝟙 (𝟙_ C) ≫ (zero : 𝟙_ C ⟶ N)) ⊗ₘ ((λ_ (𝟙_ C)).inv ≫
            (zero ⊗ₘ zero))) := by simp only [Category.id_comp,
            CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom]
        _ = (λ_ (𝟙_ C)).inv ≫ ((zero : 𝟙_ C ⟶ N) ⊗ₘ ((λ_ (𝟙_ C)).inv ≫
            (zero ⊗ₘ zero))) := by simp only [Category.id_comp]
        _ = (λ_ (𝟙_ C)).inv ≫ (((zero : 𝟙_ C ⟶ N) ≫ 𝟙 N) ⊗ₘ
            ((zero : 𝟙_ C ⟶ N) ≫ duplicate)) := by simp only [Category.comp_id, zero_duplicate]
        _ = (λ_ (𝟙_ C)).inv ≫ ((zero ⊗ₘ zero) ≫ (𝟙 N ⊗ₘ duplicate)) := by
          rw [CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom]
        _ = ((λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ zero)) ≫ (𝟙 N ⊗ₘ duplicate) := by rw [← Category.assoc]

    -- 7. Apply the postcompose recursor law to both sides!
    have h_L : (ρ_ N).hom ≫ duplicate ≫ (duplicate ⊗ₘ 𝟙 N) ≫ (α_ N N N).hom =
        prc (((λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ zero)) ≫ (duplicate ⊗ₘ 𝟙 N) ≫
        (α_ N N N).hom) (succ ⊗ₘ (succ ⊗ₘ succ)) := by
      rw [← Category.assoc, ← Category.assoc]
      rw [hom_dup]
      rw [Category.assoc, Category.assoc]
      rw [prc_postcompose _ _ comm_sq_L]
      simp

    have h_R : (ρ_ N).hom ≫ duplicate ≫ (𝟙 N ⊗ₘ duplicate) =
        prc (((λ_ (𝟙_ C)).inv ≫ (zero ⊗ₘ zero)) ≫ (𝟙 N ⊗ₘ duplicate)) (succ ⊗ₘ (succ ⊗ₘ succ)) := by
      rw [← Category.assoc, hom_dup]
      rw [prc_postcompose _ _ comm_sq_R]

    -- 8. Cancel the unitor isomorphism by establishing equality under the left multiplication
    have h_eq : (ρ_ (N (C:=C))).hom ≫ duplicate ≫ (duplicate ⊗ₘ 𝟙 N) ≫
         (α_ N N N).hom = (ρ_ N).hom ≫ duplicate ≫ (𝟙 N ⊗ₘ duplicate) := by
      rw [h_L, h_R, h_init]

    -- 8. Cancel the unitor isomorphism by establishing equality under the left multiplication
    have h_eq : (ρ_ (N (C:=C))).hom ≫ duplicate ≫ (duplicate ⊗ₘ 𝟙 N) ≫
        (α_ N N N).hom = (ρ_ N).hom ≫ duplicate ≫ (𝟙 N ⊗ₘ duplicate) := by
      rw [h_L, h_R, h_init]

    -- We drop `_ =` on the first line, and use `←` to expand the identity and unitor!
    have h_final : duplicate ≫ (duplicate ⊗ₘ 𝟙 (N (C:=C))) ≫ (α_ N N N).hom =
        duplicate ≫ (𝟙 N ⊗ₘ duplicate) := by
      calc duplicate ≫ (duplicate ⊗ₘ 𝟙 N) ≫ (α_ N N N).hom
        _ = 𝟙 N ≫ (duplicate ≫ (duplicate ⊗ₘ 𝟙 N) ≫ (α_ N N N).hom) := by simp--rw [← Category.id_comp]
        _ = ((ρ_ N).inv ≫ (ρ_ N).hom) ≫
            (duplicate ≫ (duplicate ⊗ₘ 𝟙 N) ≫ (α_ N N N).hom) := by rw [← Iso.inv_hom_id]
        _ = (ρ_ N).inv ≫ ((ρ_ N).hom ≫ duplicate ≫
            (duplicate ⊗ₘ 𝟙 N) ≫ (α_ N N N).hom) := by simp only [Category.assoc]
        _ = (ρ_ N).inv ≫ ((ρ_ N).hom ≫ duplicate ≫ (𝟙 N ⊗ₘ duplicate)) := by rw [h_eq]
        _ = ((ρ_ N).inv ≫ (ρ_ N).hom) ≫ duplicate ≫ (𝟙 N ⊗ₘ duplicate) := by simp only [Category.assoc]
        _ = 𝟙 N ≫ (duplicate ≫ (𝟙 N ⊗ₘ duplicate)) := by rw [Iso.inv_hom_id]
        _ = duplicate ≫ (𝟙 N ⊗ₘ duplicate) := by rw [Category.id_comp]

    -- Convert the whiskers in the main goal to match our explicit tensor theorem
    try rw [h_whisker_L]
    try rw [h_whisker_R]

    -- Close the goal! (We provide both directions just in case Mathlib flipped the goal)
    try exact h_final
    try exact h_final.symm


variable (P)

/-- The type of twists maps of monoidal powers of `N`. -/
def Twist : ℕ → Type v := fun k => (N^[k] ⊗ P ⟶ P ⊗ N^[k])

def twist₀ : Twist P 0 := (λ_ P).hom ≫ (ρ_ P).inv

/-- The twist map induced by the universal property of the natural number object. -/
def twist₁ : Twist P 1 := prc ((ρ_ _ ).inv ≫ (P ◁ zero)) (P ◁ succ)

instance : IsPNNO ((N : C)^[1]) zero succ where
  prc := fun {A B} f g => by
    unfold pow
    dsimp [iteratedTensor]
    apply prc f g
  zero_prc := by
    intros B f g h
    simp only [id_eq, zero_prc]
  succ_prc := by
    intros E F f g
    simp only [id_eq]
    rw [succ_prc]
  prc_uniq := by
    intros A D f g r hzero hsucc
    unfold prc
    simp only [id_eq]
    rw [IsPNNO.prc_uniq (zero:=zero) (r:=r) (succ:=succ)]
    · exact hzero
    · exact hsucc


theorem twist₁_eq_rightUnitor_hom_leftUnitor_inv : twist₁ (𝟙_ C) = (ρ_ _).hom ≫ (λ_ _).inv := by
  apply Eq.symm
  apply prc_uniq
  · simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc, id_whiskerLeft]
    nth_rw 2 [← assoc, ← assoc]
    refine ?_ =≫ _
    rw [assoc, unitors_equal]
    simp only [Iso.inv_hom_id, comp_id]
  · simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc, id_whiskerLeft]

theorem twist₁_swap : twist₁ N = prc ((λ_ _).inv ≫ (zero ▷ (N : C))) (N ◁ succ) := by
  sorry

theorem twist₁_braiding [BraidedCategory C] {P : C} :
    twist₁ P = (β_ N P).hom := by
  dsimp [twist₁, prc]
  rw [← prc_uniq]
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
  rw [tensorHom_def, assoc, prc_prcompose]
  refine (Iso.inv_comp_eq (λ_ (𝟙_ C))).mp ?_
  rw [comp_whiskerRight, assoc, succ_prc]
  have : (λ_ (𝟙_ C)).inv ≫ zero ▷ 𝟙_ C ≫ prc (zero ≫ 𝟙 N) succ ≫ succ=
  (λ_ (𝟙_ C)).inv ≫ (zero ▷ 𝟙_ C ≫ prc (zero ≫ 𝟙 N) succ) ≫ succ := by
    simp only [whiskerRight_id, comp_id, assoc]
  rw [this]
  clear this
  rw [zero_prc]
  simp only [comp_id, assoc, Iso.inv_hom_id_assoc]

theorem zero_add_one : (zero ⊗ₘ one) ≫ add = (λ_ (𝟙_ C)).hom ≫ one := by
  simp only [add, one, iter]
  rw [tensorHom_def, assoc, whiskerLeft_comp, assoc]
  rw [prc_prcompose, prc_prcompose, zero_prc]
  simp only [comp_id]

-- commutativity of addition
theorem add_comm [BraidedCategory C] : (β_ (N : C) N).hom ≫ add = add := by
  dsimp [add]
  nth_rw 2 [iter]
  apply prc_uniq
  · simp only [BraidedCategory.braiding_naturality_left_assoc,
      braiding_tensorUnit_left, iter_prc,
    assoc, comp_id]
    nth_rw 2 [← comp_id (f:= (λ_ N).hom)]
    refine (Iso.cancel_iso_hom_left (λ_ N) ((ρ_ N).inv ≫ prc zero succ) (𝟙 N)).mpr ?_
    refine (Iso.inv_comp_eq_id (ρ_ N)).mpr ?_
    apply Eq.symm
    apply prc_uniq
    simp only [whiskerRight_id, assoc, Iso.inv_hom_id, comp_id]
    refine ?_ =≫ _
    exact Eq.symm unitors_equal
    simp only [whiskerRight_id, assoc, Iso.inv_hom_id, comp_id]
  · simp only [BraidedCategory.braiding_naturality_left_assoc, iter_prc, assoc,
    Iso.cancel_iso_hom_left]
    apply Eq.symm
    apply prc_uniq
    · simp only [zero_iter_assoc]
    · rw [← assoc, succ_iter]

theorem add_zero [BraidedCategory C] : (N : C) ◁ zero ≫ add = (ρ_ N).hom := by
  rw [← add_comm]
  aesop

-- associativity of addition
theorem add_assoc :
    add ▷ (N : C) ≫ add = (α_ _ _ _).hom ≫ (N ◁ add) ≫ add := by
  dsimp [add]
  simp only [iter_prc]
  rw [← IsIso.inv_comp_eq]
  apply prc_uniq
  · simp only [whiskerRight_tensor, IsIso.Iso.inv_hom, assoc, Iso.hom_inv_id_assoc]
    rw [← assoc (zero ▷ N ▷ N) (iter succ ▷ N) (iter succ)]
    rw [← comp_whiskerRight, zero_iter]
    simp only [leftUnitor_whiskerRight, assoc, Iso.inv_hom_id_assoc]
  · simp only [whiskerRight_tensor, IsIso.Iso.inv_hom, assoc, Iso.hom_inv_id_assoc,
    Iso.cancel_iso_inv_left]
    rw [← assoc, ← comp_whiskerRight, succ_iter, comp_whiskerRight]
    rw [assoc, succ_iter]

/-- The monoid structure on the natural number object. -/
instance monObj [BraidedCategory C] : MonObj (N : C) where
  one := zero
  mul := add
  one_mul := zero_add
  mul_one := add_zero
  mul_assoc := add_assoc

instance NNO.mon [BraidedCategory C] : Mon C where
  X := N
  mon := by infer_instance

instance [BraidedCategory C] : IsCommMonObj (N : C) where
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
  isPNNO := {
    prc {P B} e a := list.prc e ((λ_ _).hom ≫ a)
    zero_prc {A B f g} := by rw [list.nil_prc]
    succ_prc {A B f g} := by
      rw [comp_whiskerRight, assoc]
      refine (IsIso.eq_inv_comp ((λ_ (list (𝟙_ C))).inv ▷ A)).mp ?_
      rw [list.cons_prc, ← assoc, ← assoc, ← assoc]
      refine ?_ =≫ g
      simp only [id_whiskerLeft, assoc,
        Iso.inv_hom_id, comp_id, leftUnitor_inv_whiskerRight,
        IsIso.inv_comp, IsIso.Iso.inv_inv]
    prc_uniq {A B f g r hnil hcons} := by
     apply list.prc_uniq r hnil
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

theorem len_eq_rc_zero_snd_succ' {A : C} :
    list.len (A:= A) = list.rc zero (snd A N ≫ succ) := by
  dsimp [list.rc]
  apply plist.rc_uniq
  · dsimp [nil,len,map,map]
    simp only [plist.nil_map]
  . dsimp [len, map, cons]
    simp only [plist.cons_map]
    refine _ ≫= ?_
    dsimp [snd,list]
    sorry
    --simp only [assoc, Iso.hom_inv_id_assoc]

theorem len_eq_rc_zero_snd_succ {A : C} :
    list.len (A:= A) = list.rc zero (snd A N ≫ succ) := by
  dsimp [list.rc]
  apply plist.rc_uniq
  · -- BASE CASE
    dsimp [nil, len, map]
    simp only [plist.nil_map]

  · -- INDUCTIVE CASE
    dsimp [len, map, cons, succ]

    -- 1. Expand the left side into its whisker components
    rw [plist.cons_map]

    -- 2. Unfold `snd` on the right side.
    -- This exposes `toUnit ▷ _ ≫ λ.hom`. The `λ.hom` and `λ.inv` will
    -- instantly annihilate each other, leaving both sides identical!
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
  sorry

instance isMonHomLen [BraidedCategory C] : IsMonHom (list.len (A:= A)) where
  one_hom := nil_len_zero
  mul_hom := append_len_add

#check Mon.Hom
/-- Promoting the length morphism to an internal monoid homomorphism from `list A` to `N`. -/
def list.lenMonHom [BraidedCategory C] {A : C} :
    Mon.Hom (List.mon A) (NNO.mon) where
  hom := list.len
  isMonHom_hom := by infer_instance

end length

end list

namespace NNO

section const

variable {C} [SemiCartesianMonoidalCategory C] [NNO C]

open SemiCartesianMonoidalCategory MorphismProperty

/-- `∀ n, f (succ n, a) = f (n, a)` implies `∀ n, f (n, a) = f (0, a)`. -/
theorem const_of_no_change_succ {P B : C} (r : N ⊗ P ⟶ B) (no_change_succ : succ ▷ P ≫ r = r) {n : 𝟙_ C ⟶ N} :
    r = constMorphismFrom (𝟙_ C) (isTerminalTensorUnit) N n ▷ P ≫ r := by
  sorry

end const

end NNO

end CategoryTheory
