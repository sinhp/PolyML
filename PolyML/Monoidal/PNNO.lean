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

universe u v

namespace CategoryTheory

namespace MonoidalCategory

open Category Opposite Limits

variable {C : Type u} [Category.{v} C]

-- SH: usually params are on the left, although this becomes incompatible with plist.
/-- Parameterized natural number object in a monoidal category. -/
class IsPNNO [MonoidalCategory C] (N : C) (zero : 𝟙_ C ⟶ N) (succ : N ⟶ N) where
  prc (zero succ) {P B : C} (f : P ⟶ B) (g : B ⟶ B) : N ⊗ P ⟶ B
  zero_prc {P B : C} {f : P ⟶ B} {g : B ⟶ B} : (zero ▷ P) ≫ prc f g = (λ_ P).hom ≫ f
  succ_prc {P B : C} {f : P ⟶ B} {g : B ⟶ B} : (succ ▷ P) ≫ prc f g = prc f g ≫ g
  prc_uniq {P B : C} {f : P ⟶ B} {g : B ⟶ B} (r : N ⊗ P ⟶ B)
    (h_zero : (zero ▷ P) ≫ r = (λ_ P).hom ≫ f) (h_succ: (succ ▷ P) ≫ r = r ≫ g) : r = prc f g

open IsPNNO

/-- Any two parameteried natural number objects in a monoidal category are isomorphic. -/
def IsPNNO.iso [MonoidalCategory C] {N N' : C} {zero : 𝟙_ C ⟶ N} {succ : N ⟶ N} {zero' : 𝟙_ C ⟶ N'} {succ' : N' ⟶ N'}
    [IsPNNO N zero succ] [IsPNNO N' zero' succ'] : N ≅ N' where
  hom := (ρ_ N).inv ≫ prc zero succ zero' succ'
  inv := (ρ_ N').inv ≫ prc zero' succ' zero succ
  hom_inv_id := sorry
  inv_hom_id := sorry

namespace IsPNNO

variable [MonoidalCategory C]

variable {N : C} {zero : 𝟙_ C ⟶ N} {succ : N ⟶ N} [IsPNNO N zero succ]

theorem congr_arg {P B : C} {f f' : P ⟶ B} {g g' : B ⟶ B}
    (h : f = f') (h' : g = g') :
    prc zero succ f g = prc zero succ f' g' := by
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

attribute [instance] PNNO.isPNNO

-- @[inherit_doc] notation "N_" => N

namespace PNNO

variable {C} [MonoidalCategory C] [PNNO C]

section

variable {P B : C}

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
  apply IsPNNO.prc_uniq
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

end

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
theorem iter_id {P : C} : iter (𝟙 P) = toUnit ▷ P ≫ (λ_ _).hom := by
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
def toBool [Bool C] : (N : C) ⟶ 𝟮_ C := (ρ_ _).inv ≫ prc Bool.ff Bool.ttConst

theorem toBool_desc_eq_toUnit [Bool C] : toBool C ≫ Bool.toUnit = toUnit := by
  refine (Iso.eq_inv_comp (ρ_ N)).mpr ?_
  rw [iter]
  apply prc_uniq
  · dsimp [toBool]
    have : zero ▷ 𝟙_ C ≫ (ρ_ N).hom ≫ ((ρ_ N).inv ≫ prc Bool.ff Bool.ttConst) ≫ Bool.toUnit =
    (zero ▷ 𝟙_ C ≫ ((ρ_ N).hom ≫ (ρ_ N).inv) ≫ prc Bool.ff Bool.ttConst) ≫ Bool.toUnit := by
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
    have : (ρ_ N).inv ≫ succ ▷ 𝟙_ C ≫ prc Bool.ff Bool.ttConst ≫ Bool.toUnit=
    (ρ_ N).inv ≫ (succ ▷ 𝟙_ C ≫ prc Bool.ff Bool.ttConst) ≫ Bool.toUnit := by
      simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
    rw [this]; clear this
    simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
    rw [← assoc,rightUnitor_inv_naturality]
    rw [assoc]
    refine _ ≫= ?_
    rw [← assoc,succ_prc]
    rw [assoc]
    refine _ ≫= ?_
    rw [Bool.ttConst_eq_toUnit_tt]
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
  exact Bool.ttConst_eq_toUnit_tt

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

variable (P : C)

/-- The type of twists maps of monoidal powers of `N`. -/
def Twist : ℕ → Type v := fun k => (N^[k] ⊗ P ⟶ P ⊗ N^[k])

def twist₀ : Twist P 0 := (λ_ P).hom ≫ (ρ_ P).inv

/-- The twist map induced by the universal property of the natural number object. -/
def twist₁ : Twist P 1 := prc ((ρ_ _ ).inv ≫ (P ◁ zero)) (P ◁ succ)

instance : IsPNNO ((N : C)^[1]) zero succ := isPNNO

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
theorem add_assoc : add ▷ (N : C) ≫ add = (α_ _ _ _).hom ≫ (N ◁ add) ≫ add := by
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

 -- g^(m + n) x = g^m (g^n x)
@[simp]
theorem iter_add {P : C} {g : P ⟶ P} :
    (add ▷ P) ≫ iter g = (α_ _ _ _).hom ≫ (N ◁ iter g) ≫ iter g := by
  dsimp [add, iter]
  rw [prc_prcompose]
  simp only [comp_id]
  sorry

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
/-- The type of global elements of  -/
abbrev GlobElem [MonoidalCategory C] [PNNO C] := 𝟙_ C ⟶ N

namespace GlobalElement

@[simps!]
instance add : Add (𝟙_ C ⟶ N) where
  add := fun m n => (λ_ _).inv ≫ (m ⊗ₘ n) ≫ PNNO.add

instance : Add (𝟙_ C ⟶ N) := by infer_instance

@[simp]
instance addZeroClass : AddZeroClass (𝟙_ C ⟶ N) where
  zero := zero
  add := Add.add
  zero_add := sorry
  add_zero := sorry

@[simp]
instance addSemigroup : AddSemigroup (𝟙_ C ⟶ N) where
  add := Add.add
  add_assoc := sorry

@[simp]
def nsmul : ℕ → (𝟙_ C ⟶ N) → (𝟙_ C ⟶ N)
  | .zero => fun _ => zero
  | (.succ m) => fun a => Add.add a (nsmul m a)

@[simp]
instance addMonoid : AddMonoid (𝟙_ C ⟶ N) where
  nsmul := nsmul
  nsmul_zero := sorry
  nsmul_succ := sorry

@[simp]
instance addCommMonoid : AddCommMonoid (𝟙_ C ⟶ N) where
  add_comm := sorry

variable (C) in
/-- The numerals as morphisms from a comonoid object to the NNO. -/
def num [MonoidalCategory C] [PNNO C] : ℕ → (𝟙_ C ⟶ N)
  | Nat.zero => addMonoid.zero
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
  sorry

theorem add_num_comm (m n : ℕ) :
    num C m + num C m = num C n + num C m := by
  sorry

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
  sorry

end GlobalElement

end PNNO

section const

open PNNO

variable [SemiCartesianMonoidalCategory C] [PNNO C]

open SemiCartesianMonoidalCategory MorphismProperty

/-- `∀ n, f (succ n, a) = f (n, a)` implies `∀ n, f (n, a) = f (0, a)`. -/
theorem PNNO.const_of_no_change_succ {P B : C} (r : N ⊗ P ⟶ B) (no_change_succ : succ ▷ P ≫ r = r) {n : 𝟙_ C ⟶ N} :
    r = constMorphismFrom (𝟙_ C) (isTerminalTensorUnit) N n ▷ P ≫ r := by
  sorry

end const

end MonoidalCategory

end CategoryTheory
