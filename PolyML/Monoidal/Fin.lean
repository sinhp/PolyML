/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import PolyML.Monoidal.NNO
import PolyML.Cartesian.NNO
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong

/-
In this file, we prove that in a list-arithmetic category, the list object `list A` is a free monoid on the object `A`.
Our development here is a categorification of `Mathlib.Algebra.FreeMonoid.Basic` for types.

Reference: Topos Theory, Peter Johnstone, Section 6.2. Finite Cardinals
-/
namespace CategoryTheory

open Category CategoryTheory NNO Functor MonoidalCategory Mon_Class SemiCartesianMonoidalCategory Limits

universe v u

-- Note: This should really work in the semicartesian case and we need to include the predicate
-- variable (C) in
-- class IsCartesianMonoidalCategory (C : Type u) [Category.{v} C] extends`
--   SemiCartesianMonoidalCategory C where
--   /-- The monoidal product is the categorical product. -/
--   tensorProductIsBinaryProduct (X Y : C) : IsLimit <| BinaryFan.mk (SemiCartesianMonoidalCategory.fst X Y) (SemiCartesianMonoidalCategory.snd X Y)
--   fst_def (X Y : C) : SemiCartesianMonoidalCategory.fst X Y = X ◁ isTerminalTensorUnit.from Y ≫ (ρ_ X).hom := by aesop_cat
--   snd_def (X Y : C) : SemiCartesianMonoidalCategory.snd X Y = isTerminalTensorUnit.from X ▷ Y ≫ (λ_ Y).hom := by aesop_cat


-- TODO: CocartesianMonoidalCategory


variable {C : Type u} [Category.{v} C] [ChosenPullbacks C]

open ChosenPullbacksAlong IsPNNO PNNO

section UnivMap

variable [MonoidalCategory C] [PNNO C]

variable (C) in
/-- The universal map with finite fibres. -/
def univFinMap : (N : C) ⊗ N ⟶ N := add ≫ succ

end UnivMap

section Fin

open ChosenPullbacksAlong IsPNNO PNNO MonoidalCategory

/-- The cardinal finite objects in a category with pullbacks and NNO.
We think of `fin n` as the the "set" of pairs `(a, b)` where `a + b + 1 = n`; There are exactly `n` such pairs.
The following diagram is a pullback square defining `fin n`:
```
fin n ------------------> 1
  |                       |
  |                       | n
  v                       v
  N × N  -------> N ----> N
          add       succ
```
The left hand side vertical morphism is a monomorphism.
-/
def fin [MonoidalCategory C] [PNNO C] (n : 𝟙_ C ⟶ N) := pullbackObj n (univFinMap C)


def isInitialFinZero [MonoidalCategory C] [PNNO C] : IsInitial (fin zero : C) := by sorry

@[simps pt]
def binaryCofan [MonoidalCategory C] [NNO C] : BinaryCofan (𝟙_ C) N where
  pt := N
  ι := {
    app := fun
          | ⟨.left⟩ => zero
          | ⟨.right⟩ => succ
    naturality := fun ⟨X⟩ ⟨Y⟩ ⟨⟨u⟩⟩ => by
      cases X  <;> cases Y <;> repeat (first | contradiction | aesop)
  }

  /-- If `N` is an NNO then `1 + N` is also an NNO. -/
noncomputable def isNNOPlusOne [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N] :
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
    -- unfold IsNNO.rc
    -- unfold NNO.prc
    refine coprod.hom_ext_iff.mpr ?_
    · rw [hr1]
      simp only [colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.mk_inl, BinaryCofan.mk_inr,
        true_and]
      -- refine (Iso.eq_inv_comp (ρ_ N)).mpr ?_
      apply isNNO.rc_uniq
      · rw [← hr1]
        simp only [assoc]
        rw [← hr2]
        simp only [coprod.desc_comp, assoc, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.mk_inl]
      · rw [assoc]
        rw [← hr2]
        simp only [coprod.desc_comp, assoc, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.mk_inr]

/-- `N` is isomorphic to `1 + N`. -/
noncomputable def NNOIsoPlusOne [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N] :
    NNO.N ≅ (𝟙_ C ⨿ N) := by
  apply IsNNO.iso (NNO.isNNO) (isNNOPlusOne)

theorem NNOIsoPlusOne_inv [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N] :
    (NNOIsoPlusOne).inv = coprod.desc (NNO.zero : 𝟙_ C ⟶ N) NNO.succ := by
  --have := IsColimit.uniq _
  --rw [coprod.desc, colimit.desc, colimit.isColimit]
  -- rw [IsColimit.uniq]
  sorry

#check CategoryTheory.Limits.coprod.desc'

/-- The diagram `𝟙_C ⟶ N ⟵ N`  is a coproduct diagram. -/
noncomputable def colimitCocone [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N] :
  ColimitCocone (pair (𝟙_ C) N) where
    cocone := binaryCofan
    isColimit := by
      refine BinaryCofan.IsColimit.mk (C:= C) ?_ ?_ ?_ ?_ ?_
      · intro S a b
        exact NNOIsoPlusOne.hom ≫ (coprod.desc a b)
      · sorry
      · sorry
      · sorry

/-- The diagram `T_C ⟶ N ⟵ N` is a colimit diagram. -/
def BinaryCoproduct [MonoidalCategory C] [NNO C] [HasBinaryCoproduct (𝟙_ C) N] : HasBinaryCoproduct (𝟙_ C) N where
  exists_colimit := by
    constructor
    exact colimitCocone

#check CartesianMonoidalCategory


noncomputable def finZeroIso [MonoidalCategory C] [PNNO C] [HasInitial C] : fin zero ≅ ⊥_ C :=
  IsInitial.uniqueUpToIso isInitialFinZero initialIsInitial

/-- fin (n + 1) ≅ fin n + 1 -/
def finSuccIso [MonoidalCategory C] [PNNO C] [HasBinaryCoproducts C] (n : 𝟙_ C ⟶ N) : fin (n ≫ succ) ≅ 𝟙_ C ⨿ fin n := by
  sorry

/-- fin 1 ≅ 1 -/
def isTerminalFinOne [MonoidalCategory C] [PNNO C] : IsTerminal (fin one : C) := by sorry

def pairing [MonoidalCategory C] [PNNO C] (m n : 𝟙_ C ⟶ N) : 𝟙_ C ⟶ N ⊗ N :=
  (ρ_ _).inv ≫ (m ⊗ₘ n)

/-- fin (m + n ) ≅ fin m + fin n -/
def finSumIso [MonoidalCategory C] [PNNO C] [HasBinaryCoproducts C] (m n : 𝟙_ C ⟶ N) :
    fin (pairing m n ≫ add) ≅ fin m ⨿ fin n := by
  sorry

/-- fin (m . n) ≅ fin m ⊗ fin n -/
def finProdIso [CartesianMonoidalCategory C] [PNNO C] [HasBinaryCoproducts C] (m n : 𝟙_ C ⟶ N) :
    fin (pairing m n ≫ mul') ≅ fin m ⊗ fin n := by
  sorry

/-- fin (m ^ n) ≅ fin m ^ fin n -/
def finExpIso [CartesianMonoidalCategory C] [CartesianClosed C] [PNNO C] (m n : 𝟙_ C ⟶ N) :
    fin (pairing m n ≫ mul') ≅ (fin m) ^^ (fin n) := by
  sorry

end Fin


-- The universal map with finite fibres
-- need to define the object `N<`  of pairs of natural numbers (m,n) where
-- m < n. So, basically, `N< = { (m,n) : N × N | m < n }`.
-- The universal map is the first projection from `N<` to `N`. It takes
-- a pair `(m,n)` to `m`.
-- The fibre over `m` is the object `fin (succ m)`, which has cardinality `m + 1`.


/--
```
finLt ------------------> 1
  |                       |
  |                       | true
  v                       v
  N × N  ---------------> bool
              lt
```
-/
noncomputable abbrev finLt [CartesianMonoidalCategory C] [PNNO C] [HasBinaryCoproducts C] := pullbackObj (C:= C) bool.true lt

def univFinMapIso [CartesianMonoidalCategory C] [PNNO C] [HasBinaryCoproducts C] :
    Over.mk (univFinMap C) ≅ Over.mk (pullback.snd (C:= C) bool.true lt ≫ fst N N) := by
  sorry

/--
The following square is a pullback square:
```
              ext
      E -----------------> finLt
      |                   |
      |                   | fstProj
      v                   v
      B  ---------------> N
            fibCard
```
-/
class FiniteFibres [MonoidalCategory C] [PNNO C] [HasBinaryCoproducts C] {E B : C} (p : E ⟶ B) where
  fibCard : B ⟶ N
  ext : E ⟶ N ⊗ N
  isPullback : IsPullback (ext) p (univFinMap C) (fibCard)

/--
By pullback pasting lemmas the following square is also a pullback square:
```
fin b ---->  E  --------------> finLt
 |            |                   |
 |            |                   | fstProj
 |            v                   v
 1 -------->  B  ---------------> N
      b            fibCard
```
-/
def fibre [MonoidalCategory C] {E B : C} (p : E ⟶ B) (b : 𝟙_ C ⟶ B) : C :=
  pullbackObj (C:= C) p b

/-- The tautological instance showing that `finLtToNNO` has finite fibres. -/
instance [MonoidalCategory C] [PNNO C] [HasBinaryCoproducts C] : FiniteFibres (univFinMap C) where
  fibCard := sorry
  ext := sorry
  isPullback := sorry

def fibreOfFiniteFibresIsCardinalFinite [MonoidalCategory C] [PNNO C] [HasBinaryCoproducts C]
    {E B : C} {p : E ⟶ B} [FiniteFibres p]
    (b :  𝟙_ C ⟶ B) :
    fibre p b  ≅ fin (b ≫ FiniteFibres.fibCard p) := by
  sorry

  --fibIso : ∀ (b : 𝟙_ C ⟶ B), fin (fibCard ≫ b) ≅ pullback f b


-- def finPair (m n : 𝟙_ C ⟶ N) : 𝟙_ C ⟶ N × N :=
--   (ρ_ _).inv ≫ (m ⊗ₘ n)


/-- For an object `X : C`, the structure `FinEnum X` consists of a natural number `n` and an
isomorphism `X ≅ nno.fin n`. This means that `X` is finite and can be enumerated in some order. -/
class FinEnum [MonoidalCategory C] [PNNO C] (X : C) where
  card : 𝟙_ C ⟶ N
  iso : X ≅ fin card

end CategoryTheory
