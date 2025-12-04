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


variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [NNO C] [ChosenPullbacks C]

open ChosenPullbacksAlong


variable (C) in
/-- The universal map with finite fibres. -/
def univFinMap : (N : C) ⊗ N ⟶ N := add ≫ succ

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
def fin (n : 𝟙_ C ⟶ N) := pullbackObj n (univFinMap C)

def isInitialFinZero : IsInitial (fin zero : C) := by sorry

@[simps pt]
def binaryCofan : BinaryCofan (𝟙_ C) N where
  pt := N
  ι := {
    app := fun
          | ⟨.left⟩ => zero
          | ⟨.right⟩ => succ
    naturality :=  fun ⟨X⟩ ⟨Y⟩ ⟨⟨u⟩⟩ => by
      cases X; cases Y
      · dsimp [pair, BinaryCofan]
        simp only [Discrete.functor_map_id, Discrete.functor_obj_eq_as, id_comp, comp_id]
      · simp only [pair_obj_left, const_obj_obj, pair_obj_right, const_obj_map, comp_id]
        grind only
      · cases Y
        · grind
        · simp only [pair_obj_right, const_obj_obj, Discrete.id_def', Discrete.functor_map_id,
          id_comp, comp_id]
  }

def isNNOPlusOne [HasBinaryCoproduct (𝟙_ C) N] :
    IsNNO (𝟙_ C ⨿ N) (coprod.inl) (coprod.desc zero succ ≫ coprod.inr) where
  rc := sorry
  zero_rc := sorry
  succ_rc := sorry
  rc_uniq := sorry


#check HasBinaryCoproduct

noncomputable def finZeroIso [HasInitial C] : fin zero ≅ ⊥_ C :=
  IsInitial.uniqueUpToIso isInitialFinZero initialIsInitial

/-- fin (n + 1) ≅ fin n + 1 -/
def finSuccIso [HasBinaryCoproducts C] (n : 𝟙_ C ⟶ N) : fin (n ≫ succ) ≅ 𝟙_ C ⨿ fin n := by
  sorry

/-- fin 1 ≅ 1 -/
def isTerminalFinOne : IsTerminal (fin one : C) := by sorry

def pairing (m n : 𝟙_ C ⟶ N) : 𝟙_ C ⟶ N ⊗ N :=
  (ρ_ _).inv ≫ (m ⊗ₘ n)

/-- fin (m + n ) ≅ fin m + fin n -/
def finSumIso [HasBinaryCoproducts C] (m n : 𝟙_ C ⟶ N) :
    fin (pairing m n ≫ NNO.add) ≅ fin m ⨿ fin n := by
  sorry

/-- fin (m . n) ≅ fin m ⊗ fin n -/
def finProdIso [HasBinaryCoproducts C] (m n : 𝟙_ C ⟶ N) :
    fin (pairing m n ≫ NNO.mul') ≅ fin m ⊗ fin n := by
  sorry

/-- fin (m ^ n) ≅ fin m ^ fin n -/
def finExpIso [CartesianClosed C] (m n : 𝟙_ C ⟶ N) :
    fin (pairing m n ≫ mul') ≅ (fin m) ^^ (fin n) := by
  sorry

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
noncomputable abbrev finLt [HasBinaryCoproducts C] := pullback (C:= C) bool.true NNO.lt

def univFinMapIso [HasBinaryCoproducts C] :
    Over.mk (univFinMap C) ≅ Over.mk (pullback.snd (C:= C) bool.true NNO.lt ≫ fst N N) := by
  sorry

variable (C) in
noncomputable def univFinMap' [HasBinaryCoproducts C] : finLt ⟶ (N : C) :=
  pullback.snd (C:= C) bool.true NNO.lt ≫ fst N N

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
class FiniteFibres [HasBinaryCoproducts C] {E B : C} (p : E ⟶ B) where
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
def fibre {E B : C} (p : E ⟶ B) (b : 𝟙_ C ⟶ B) : C :=
  pullbackObj (C:= C) p b

/-- The tautological instance showing that `finLtToNNO` has finite fibres. -/
instance [HasBinaryCoproducts C] : FiniteFibres (univFinMap C) := sorry

def fibreOfFiniteFibresIsCardinalFinite [HasBinaryCoproducts C] {E B : C} {p : E ⟶ B} [FiniteFibres p]
    (b :  𝟙_ C ⟶ B) :
    fibre p b  ≅ fin (b ≫ FiniteFibres.fibCard p) := by
  sorry

  --fibIso : ∀ (b : 𝟙_ C ⟶ B), fin (fibCard ≫ b) ≅ pullback f b


-- def finPair (m n : 𝟙_ C ⟶ N) : 𝟙_ C ⟶ N × N :=
--   (ρ_ _).inv ≫ (m ⊗ₘ n)


/-- For an object `X : C`, the structure `FinEnum X` consists of a natural number `n` and an
isomorphism `X ≅ nno.fin n`. This means that `X` is finite and can be enumerated in some order. -/
class FinEnum (X : C) where
  card : 𝟙_ C ⟶ N
  iso : X ≅ fin card

end CategoryTheory
