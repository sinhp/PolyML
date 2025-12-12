/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.Tactic.CategoryTheory.Coherence
import PolyML.ForMathlib.Bool
import PolyML.ForMathlib.Monoidal.AddMon_
import PolyML.ForMathlib.Monoidal.Powers
import PolyML.Monoidal.ListArithmetic

set_option linter.unusedSectionVars false

universe u v

namespace CategoryTheory

open Category Opposite MonoidalCategory Limits

variable {C : Type u} [Category.{v} C]

-- SH: usually params are on the left, although this becomes incompatible with plist.
/-- Parameterized natural number object in a monoidal category. -/
structure IsPNNO [MonoidalCategory C] (N : C) (zero : 𝟙_ C ⟶ N) (succ : N ⟶ N) where
  prc {zero succ} {P B : C} (f : P ⟶ B) (g : B ⟶ B) : N ⊗ P ⟶ B
  zero_prc {P B : C} {f : P ⟶ B} {g : B ⟶ B} : (zero ▷ P) ≫ prc f g = (λ_ P).hom ≫ f
  succ_prc {P B : C} {f : P ⟶ B} {g : B ⟶ B} : (succ ▷ P) ≫ prc f g = prc f g ≫ g
  prc_uniq {P B : C} {f : P ⟶ B} {g : B ⟶ B} (r : N ⊗ P ⟶ B)
    (h_zero : (zero ▷ P) ≫ r = (λ_ P).hom ≫ f) (h_succ: (succ ▷ P) ≫ r = r ≫ g) : r = prc f g

/-- Natural number object in a monoidal category. -/
structure IsNNO [MonoidalCategory C] (N : C) (zero : 𝟙_ C ⟶ N) (succ : N ⟶ N) where
  rc {zero succ} {B : C} (f : 𝟙_ C ⟶ B) (g : B ⟶ B) : N ⟶ B
  zero_rc {B : C} {f : 𝟙_ C ⟶ B} {g : B ⟶ B} : zero ≫ rc f g = f
  succ_rc {B : C} {f : 𝟙_ C ⟶ B} {g : B ⟶ B} : succ ≫ rc f g = rc f g ≫ g
  rc_uniq {B : C} {f : 𝟙_ C ⟶ B} {g : B ⟶ B} (r : N ⟶ B)
    (h_zero : zero ≫ r = f) (h_succ : succ ≫ r = r ≫ g) : r = rc f g

/-- Every parameterized natural number object in a monoidal closed category is a natural number object. -/
def IsPNNO.toIsNNO [MonoidalCategory C] (N : C) (zero : 𝟙_ C ⟶ N) (succ : N ⟶ N)
    (pnno : IsPNNO N zero succ) : IsNNO N zero succ where
  rc := fun {B} f g => (ρ_ N).inv ≫ pnno.prc f g
  zero_rc := by
    intros B f g
    simp only [← assoc]
    rw [rightUnitor_inv_naturality]
    simp only [assoc]
    rw [pnno.zero_prc]
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
    (nno : IsNNO N zero succ) : IsPNNO N zero succ where
  prc := fun {P B} f g => (β_ N P).hom ≫
      (MonoidalClosed.uncurry <| nno.rc ((MonoidalClosed.curry (ρ_ P).hom) ≫ (ihom P).map f) ((ihom P).map g))
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

/-- Any two parameteried natural number objects in a monoidal category are isomorphic. -/
def IsPNNO.iso [MonoidalCategory C] {N N' : C} {zero : 𝟙_ C ⟶ N} {succ : N ⟶ N} {zero' : 𝟙_ C ⟶ N'} {succ' : N' ⟶ N'}
    (pnno : IsPNNO N zero succ) (pnno' : IsPNNO N' zero' succ') : N ≅ N' where
  hom := (ρ_ N).inv ≫ pnno.prc zero' succ'
  inv := (ρ_ N').inv ≫ pnno'.prc zero succ
  hom_inv_id := sorry
  inv_hom_id := sorry


/-- Any two natural number objects in a monoidal category are isomorphic. -/
def IsNNO.iso [MonoidalCategory C] {N N' : C} {zero : 𝟙_ C ⟶ N} {succ : N ⟶ N} {zero' : 𝟙_ C ⟶ N'} {succ' : N' ⟶ N'}
    (nno : IsNNO N zero succ) (nno' : IsNNO N' zero' succ') : N ≅ N' :=
  sorry

namespace IsPNNO

variable [MonoidalCategory C]

variable {N : C} {zero : 𝟙_ C ⟶ N} {succ : N ⟶ N} (pnno : IsPNNO N zero succ)

theorem congr_arg {P B : C} {f f' : P ⟶ B} {g g' : B ⟶ B}
    (h : f = f') (h' : g = g') :
    pnno.prc f g = pnno.prc f' g' := by
  subst h h'
  rfl

end IsPNNO

variable (C)

/-- A natural number object in a monoidal category. -/
class PNNO [MonoidalCategory C] where
  /-- The (left) parameterized natural number object. -/
  N : C
  /-- The zero morphism. -/
  zero : 𝟙_ C ⟶ N
  /-- The successor morphism. -/
  succ : N ⟶ N
  /-- The parameterized natural number object satisfies the properties of a left natural number object. -/
  [isPNNO : IsPNNO N zero succ]

-- @[inherit_doc] notation "N_" => PNNO.N

namespace PNNO

open IsPNNO

variable {C} [MonoidalCategory C] [PNNO C] {P B : C}

def prc (f : P ⟶ B) (g : B ⟶ B) : N ⊗ P ⟶ B :=
  isPNNO.prc f g

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
def rc (f : 𝟙_ C ⟶ B) (g : B ⟶ B) : N ⟶ B :=
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

/-- Mapping the NNO to the unit of the monoidal category.
Note: toUnit here is different than `SemiCartesianMonoidalCategory.toUnit`.
`𝟙_ C` is not neccessarily a terminal object.
-/
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
def toBool [Bool C] : (N : C) ⟶ 𝟮_ C := (ρ_ _).inv ≫ prc Bool.ff Bool.constTrue

theorem toBool_desc_eq_toUnit [Bool C] : toBool C ≫ Bool.toUnit = toUnit := by
  refine (Iso.eq_inv_comp (ρ_ N)).mpr ?_
  rw [iter]
  apply prc_uniq
  · dsimp [toBool]
    have : zero ▷ 𝟙_ C ≫ (ρ_ N).hom ≫ ((ρ_ N).inv ≫ prc Bool.ff Bool.constTrue) ≫ Bool.toUnit =
    (zero ▷ 𝟙_ C ≫ ((ρ_ N).hom ≫ (ρ_ N).inv) ≫ prc Bool.ff Bool.constTrue) ≫ Bool.toUnit := by
      simp only [whiskerRight_id, assoc, Iso.hom_inv_id_assoc]
    rw [this]
    simp only [ Iso.hom_inv_id, id_comp, comp_id]
    rw [zero_prc]
    rw [unitors_equal, Bool.toUnit, Bool.elim]
    simp_all only [assoc, IsBool.ff_elim, comp_id]
  · simp only [whiskerRight_id, assoc, comp_id]
    have : (ρ_ N).hom ≫ succ ≫ (ρ_ N).inv ≫ (ρ_ N).hom ≫ toBool C ≫ Bool.toUnit =
    (((ρ_ N).hom ≫ succ) ≫ (ρ_ N).inv) ≫ (((ρ_ N).hom) ≫ toBool C ≫ Bool.toUnit) := by
      simp only [assoc, Iso.inv_hom_id_assoc]
    rw [this]; clear this
    rw [rightUnitor_inv_naturality]
    simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
    rw [← assoc]
    dsimp [toBool]
    rw [← assoc]
    rw [rightUnitor_inv_naturality]
    rw [assoc, assoc]
    have : (ρ_ N).inv ≫ succ ▷ 𝟙_ C ≫ prc Bool.ff Bool.constTrue ≫ Bool.toUnit=
    (ρ_ N).inv ≫ (succ ▷ 𝟙_ C ≫ prc Bool.ff Bool.constTrue) ≫ Bool.toUnit := by
      simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
    rw [this]; clear this
    simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
    rw [← assoc,rightUnitor_inv_naturality]
    rw [assoc]
    refine _ ≫= ?_
    rw [← assoc,succ_prc]
    rw [assoc]
    refine _ ≫= ?_
    rw [Bool.constTrue_eq_toUnit_true]
    dsimp [Bool.toUnit, Bool.elim, Bool.true]
    simp_all only [Bool.elim_comp, id_comp, IsBool.tt_elim]

/-- Converts a boolean value to a natural number, sending `bool.false` to `0` and `bool.true` to `1`. -/
def fromBool [Bool C] : 𝟮_ C ⟶ (N : C) := Bool.elim zero one

variable {C}

theorem zero_toBool [Bool C] :
    zero ≫ toBool C = Bool.ff := by
  dsimp [toBool]
  rw [← assoc, rightUnitor_inv_naturality]
  rw [assoc, zero_prc]
  refine (Iso.inv_comp_eq (ρ_ (𝟙_ C))).mpr ?_
  refine ?_ =≫ _
  exact unitors_equal

theorem succ_toBool [Bool C] :
    succ ≫ toBool C = toUnit ≫ Bool.tt := by
  rw [← toBool_desc_eq_toUnit]
  unfold toBool
  rw [← assoc, rightUnitor_inv_naturality, assoc, assoc, assoc]
  refine _ ≫= ?_
  rw [← assoc]
  rw [succ_prc, assoc]
  refine _ ≫= ?_
  exact Bool.constTrue_eq_toUnit_true

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
def twist₁ : Twist P 1 := prc ((ρ_ _ ).inv ≫ (P ◁ zero)) (P ◁ succ)

example : IsPNNO ((N : C)^[1]) zero succ := isPNNO

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
instance addMonObj [BraidedCategory C] : AddMonObj (N : C) where
  zero := zero
  add := add
  zero_add := zero_add
  add_zero := add_zero
  add_assoc := add_assoc

instance addMon [BraidedCategory C] : AddMon C where
  X := N
  addMon := by infer_instance

instance isAddCommMonObj [BraidedCategory C] : IsAddCommMonObj (N : C) where
  add_comm := add_comm

def iterCurried {P : C} [Closed P] [BraidedCategory C] (f : P ⟶ P) : N ⟶ (P ⟶[C] P) :=
  (MonoidalClosed.curry <| (β_ _ _).hom ≫ iter f)

variable (C) in
/-- The type of global elements of PNNO. -/
abbrev GlobElem [MonoidalCategory C] [PNNO C] := 𝟙_ C ⟶ N

namespace GlobalElement

@[simps!]
instance add : Add (𝟙_ C ⟶ N) where
  add := fun m n => (ρ_ _).inv ≫ (m ⊗ₘ n) ≫ PNNO.add

@[simp]
instance addZeroClass [BraidedCategory C] : AddZeroClass (𝟙_ C ⟶ N) where
  zero := zero
  add := Add.add
  zero_add a := by
    simp only [add_add]
    rw [tensorHom_def']
    simp only [id_whiskerLeft, assoc]
    rw [unitors_equal]
    simp only [Iso.inv_hom_id_assoc]
    simp only [← assoc]
    rw [leftUnitor_inv_naturality]
    have  :  a ≫ 𝟙 N  = a := by simp only [comp_id]
    simp only [id_whiskerLeft, Iso.inv_hom_id_assoc, assoc]
    nth_rw 2 [← this]
    congr
    (expose_names; exact (Iso.inv_comp_eq_id (λ_ N)).mpr (PNNO.zero_add (C:=C)))
  add_zero a := by
    simp only [add_add]
    rw [tensorHom_def]
    simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
    have  :  a ≫ 𝟙 N  = a := by simp
    nth_rw 2 [← this]
    congr
    have := PNNO.add_zero (C:=C)
    exact (Iso.inv_comp_eq_id (ρ_ N)).mpr this

@[simp]
instance addSemigroup [BraidedCategory C] : AddSemigroup (𝟙_ C ⟶ N) where
  add := Add.add
  add_assoc {a b c} := by
    sorry

@[simp]
def nsmul : ℕ → (𝟙_ C ⟶ N) → (𝟙_ C ⟶ N)
  | .zero => fun _ => zero
  | .succ m => fun a => Add.add (nsmul m a) a

@[simp]
instance addMonoid [BraidedCategory C]: AddMonoid (𝟙_ C ⟶ N) where
  zero := zero
  nsmul := nsmul
  add_assoc a b c := addSemigroup.add_assoc a b c
  nsmul_zero x := rfl
  nsmul_succ n x := by sorry
  zero_add a := addZeroClass.zero_add a
  add_zero a := addZeroClass.add_zero a

@[simp]
instance addCommMonoid [BraidedCategory C] : AddCommMonoid (𝟙_ C ⟶ N) where
  zero := zero
  zero_add a := CategoryTheory.PNNO.GlobalElement.addZeroClass.zero_add a
  add_zero a := CategoryTheory.PNNO.GlobalElement.addZeroClass.add_zero a
  add_assoc a b c := CategoryTheory.PNNO.GlobalElement.addSemigroup.add_assoc a b c
  nsmul := nsmul
  nsmul_zero x := rfl
  nsmul_succ n f :=CategoryTheory.PNNO.GlobalElement.addMonoid.nsmul_succ n f
  add_comm a b := sorry


end GlobalElement

variable (C) in
/-- The numerals as morphisms from the unit object to the NNO. -/
def num [MonoidalCategory C] [PNNO C] : ℕ → (𝟙_ C ⟶ N)
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

@[simp]
theorem num_add (m n : ℕ) :
    num C m + num C n = num C (m + n) := by
dsimp [num]
nth_rw 1 [← unitors_inv_equal]
refine (Iso.inv_comp_eq (λ_ (𝟙_ C))).mpr ?_
rw [← leftUnitor_naturality]
simp only [id_whiskerLeft, assoc, Iso.inv_hom_id, comp_id]
have := triangle (C:=C) (X:=𝟙_ C) (Y:=𝟙_ C)
simp only [id_whiskerLeft, Iso.hom_inv_id, comp_id, whiskerRight_id] at this
rw [tensorHom_def']
simp only [assoc]
dsimp [add]
unfold num
split
· rename_i N m
  split
  · rename_i N k
    · simp only [id_whiskerLeft, zero_iter, assoc, Iso.inv_hom_id, comp_id]
      -- simp only [iter_prc]
      -- simp only [← assoc]
      -- rw [rightUnitor_inv_naturality]
      -- rw [comp_whiskerRight]
      -- simp only [assoc]
      -- rw [zero_prc]
      -- simp only [whiskerRight_id, Iso.hom_inv_id, comp_id, Iso.inv_hom_id_assoc]
  · rename_i k l
    rw [comp_whiskerRight]
    simp only [assoc]
    rw [succ_iter]
    simp only [← assoc]
    refine ?_ =≫ _
    simp only [id_whiskerLeft, assoc, Iso.cancel_iso_hom_left]
    simp only [← assoc]
    rw [leftUnitor_inv_naturality]
    simp only [assoc]
    simp only [id_whiskerLeft, assoc]
    have:
    (λ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom ≫ zero ≫
        (λ_ PNNO.N).inv ≫ num C l ▷ PNNO.N ≫ iter succ
    = (λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).hom ≫ (zero ≫
        (λ_ PNNO.N).inv)) ≫ num C l ▷ PNNO.N≫ iter succ := by {simp only [assoc]}
    rw [this];clear this
    rw [← leftUnitor_naturality]
    simp only [whiskerLeft_comp]
    simp only [assoc]
    have :(λ_ (𝟙_ C ⊗ PNNO.N)).hom ≫ num C l ▷ PNNO.N ≫ iter succ=
    ((λ_ (𝟙_ C ⊗ PNNO.N)).hom ≫ num C l ▷ PNNO.N) ≫ iter succ := by simp
    rw [this]; clear this
    rw [← leftUnitor_naturality]
    simp only [assoc]
    have : (λ_ (𝟙_ C)).inv ≫
    𝟙_ C ◁ zero ≫ 𝟙_ C ◁ (λ_ PNNO.N).inv ≫
     𝟙_ C ◁ num C l ▷ PNNO.N ≫ (λ_ (PNNO.N ⊗ PNNO.N)).hom ≫ iter succ
     = (λ_ (𝟙_ C)).inv ≫
    (𝟙_ C ◁ zero ≫ 𝟙_ C ◁ (λ_ PNNO.N).inv ≫
    𝟙_ C ◁ num C l ▷ PNNO.N) ≫ (λ_ (PNNO.N ⊗ PNNO.N)).hom ≫ iter succ := by simp
    rw [this]
    rw [← whiskerLeft_comp]
    rw [← whiskerLeft_comp]
    simp only [whiskerLeft_comp, id_whiskerLeft, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, assoc]
    sorry
· sorry

theorem add_num_comm (m n : ℕ) :
    num C m + num C n = num C n + num C m := by
  rw [num_add, num_add, Nat.add_comm]

end Num

@[simps]
instance ofNat {n : ℕ} : OfNat (𝟙_ C ⟶ N) n where
  ofNat := num C n

#check (3 : 𝟙_ C ⟶ N)
#reduce (3 : 𝟙_ C ⟶ N)

#check (3 : 𝟙_ C ⟶ N) + (3 : 𝟙_ C ⟶ N)

#reduce (3 : 𝟙_ C ⟶ N) + (3 : 𝟙_ C ⟶ N)

example : (1 : 𝟙_ C ⟶ N) + (1 : 𝟙_ C ⟶ N) = (2 : 𝟙_ C ⟶ N) := by
  dsimp [num]
  simp [add]
  simp [iter]
  sorry

end PNNO

open PNNO

/-- Every list-arithmetic category has a natural number object. -/
@[simps]
instance arithmeticOfListArithmetic [MonoidalCategory C] [ListArithmetic C] : PNNO C where
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

theorem len_eq_rc_zero_snd_succ {A : C} :
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

attribute [local instance] CategoryTheory.AddMonObj.toMonObj

/-- The length function is a monoid homomorphism from the list monoid to the natural number object. -/
instance isMonHomLen [BraidedCategory C] : IsMonHom (list.len (A:= A)) where
  one_hom := nil_len_zero
  mul_hom := append_len_add

/-- Promoting the length morphism to an internal monoid homomorphism from `list A` to `N`. -/
def list.lenMonHom [BraidedCategory C] {A : C} :
    Mon.Hom (List.mon A) (PNNO.addMon.toMon) where
  hom := list.len
  isMonHom_hom := by infer_instance

end length

end list

namespace PNNO

section const

variable {C} [SemiCartesianMonoidalCategory C] [PNNO C]

open SemiCartesianMonoidalCategory MorphismProperty

/-- `∀ n, f (succ n, a) = f (n, a)` implies `∀ n, f (n, a) = f (0, a)`. -/
theorem const_of_no_change_succ {P B : C} (r : N ⊗ P ⟶ B) (no_change_succ : succ ▷ P ≫ r = r) {n : 𝟙_ C ⟶ N} :
    r = constMorphismFrom (𝟙_ C) (isTerminalTensorUnit) N n ▷ P ≫ r := by
  sorry

end const

end PNNO

class NNO [MonoidalCategory C] where
  /-- The (left) natural number object. -/
  N : C
  /-- The zero morphism. -/
  zero : 𝟙_ C ⟶ N
  /-- The successor morphism. -/
  succ : N ⟶ N
  /-- The natural number object satisfies the properties of a left natural number object. -/
  [isNNO : IsNNO N zero succ]

@[simps]
def PNNO.toNNO [MonoidalCategory C] [PNNO C] : NNO C where
  N := PNNO.N
  zero := PNNO.zero
  succ := PNNO.succ
  isNNO := isPNNO.toIsNNO

namespace NNO

open IsNNO

variable {C} [MonoidalCategory C] [NNO C] {B : C}

def rc (f : 𝟙_ C ⟶ B) (g : B ⟶ B) : N ⟶ B :=
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

open bool coprod

variable (C)

/-- Decides if a natural number is zero or not, if zero returns `bool.false` else it returns `bool.true`. -/
def toBool [Bool C] : (N : C) ⟶ 𝟮_ C := rc Bool.ff Bool.constTrue

/-- Converts a boolean value to a natural number, sending `bool.false` to `0` and `bool.true` to `1`. -/
def fromBool [Bool C] : 𝟮_ C ⟶ N := Bool.elim zero one

variable {C}

theorem zero_toBool [Bool C] :
    zero ≫ toBool C = Bool.ff := by
  dsimp [toBool, Bool.ff]
  rw [zero_rc]

open Bool

@[simp]
theorem true_fromBool [Bool C] :
    Bool.tt ≫ fromBool C = one := by
  simp only [fromBool, IsBool.tt_elim]

@[simp]
theorem false_fromBool [Bool C] :
    Bool.ff ≫ fromBool C = zero := by
  simp only [fromBool, IsBool.ff_elim]

theorem succ_toBool [Bool C] :
    succ ≫ toBool C = toUnit ≫ Bool.tt := by
  dsimp [toBool]
  rw [succ_rc]
  nth_rw 2
  [constTrue_eq_toUnit_true]
  dsimp [toUnit]
  dsimp [const]
  simp only [← assoc]
  congr
  apply rc_uniq
  · simp only [← assoc]
    simp only [zero_rc]
    dsimp [Bool.toUnit]
    simp only [IsBool.ff_elim]
  · simp only [comp_id]
    simp only [← assoc]
    rw [succ_rc]
    simp only [assoc]
    congr
    exact constTrue_toUnit

theorem fromBool_toBool [Bool C] :
    fromBool C ≫ toBool C = 𝟙 (𝟮_ C) := by
  ext
  · simp only [← assoc, false_fromBool, zero_toBool, comp_id]
  · congr
    dsimp [fromBool, toBool]
    simp only [elim_comp, zero_rc]
    symm
    apply IsBool.elim_uniq
    simp only [comp_id]
    simp only [comp_id]
    dsimp [one]
    simp only [assoc]
    rw [succ_rc,← assoc,zero_rc]
    dsimp [constTrue]
    simp only [IsBool.ff_elim]

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
        _root_.true_and]
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
  rw [succ_rc]
  simp only [← assoc]
  congr
  symm
  apply isNNO.rc_uniq
  · simp only [← assoc]
    have := zero_rc (C:=C) (f:=b) (g:=g)
    dsimp [rc] at this
    rw [this]
  · have := succ_rc (C:=C) (f:=b) (g:=g)
    simp only [← assoc]
    dsimp [rc] at this
    rw [← this]

@[simp]
theorem zero_succ_inr_isNNOOnePlus_rc [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N]
    {B : C} (b : 𝟙_ C ⟶ B) (g : B ⟶ B) :
    zero ≫ succ ≫ inr ≫ isNNOOnePlus.rc b g = b ≫ g ≫ g  := by
  rw [succ_inr_isNNOOnePlus_rc]
  rw [← assoc]
  rw [IsNNO.zero_rc]

/-- `N` is isomorphic to `1 + N`. -/
noncomputable def NNOIsoOnePlus [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N] :
    NNO.N ≅ (𝟙_ C ⨿ N) := by
  apply IsNNO.iso (NNO.isNNO) (isNNOOnePlus)

theorem NNOIsoOnePlus_inv [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N] :
    (NNOIsoOnePlus).inv = coprod.desc (NNO.zero : 𝟙_ C ⟶ N) NNO.succ := by
  rw [coprod.desc]
  -- have := IsColimit.uniq (C:=C) (F:=(pair (𝟙_ C) N)) (s:=(BinaryCofan.mk zero succ))
  -- rw [← CategoryTheory.Limits.colimit.isColimit_desc]
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
