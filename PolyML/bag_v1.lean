import PolyML.ListArithmetic
import Mathlib
import PolyML.ForMathlib.Regularv0

universe u v

noncomputable section
namespace CategoryTheory

open Functor Opposite Limits MonoidalCategory
  CartesianMonoidalCategory Recursive ListArithmetic Category

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local instance]
  _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

open Endofunctor Algebra

variable (U : C)

#check Regular

#check CategoryTheory.Factorisation


variable {C}

#check Quot

#check WalkingParallelPair

/-
define internal relations in categories. more or
less following definition 6 of Carboni-Vitale.
Def 2.4.2 of Mathis Menni's thesis
-/
structure EquivRel [HasPullbacks C] (X : C) where
  R : C
  (left right : R ⟶ X)
  jointly_monic : Mono (prod.lift left right)
  reflexive : ∃ (r : X ⟶ R), r ≫ left = 𝟙 X ∧ r ≫ right = 𝟙 X
  symmetric : ∃ (s : R ⟶ R), s ≫ left = right ∧ s ≫ right = left
  transitive : ∃ (t : pullback left right ⟶ R),
    pullback.fst left right ≫ right = t ≫ right ∧
    pullback.snd left right ≫ left = t ≫ left

def effectiveEquivRel {X : C} [HasPullbacks C] (ρ : EquivRel X) :=
  ∃ (Y : C) (f : X ⟶ Y), IsKernelPair f ρ.left ρ.right

variable (C)

class Exact extends Regular C where
  exact : ∀ (X : C) (ρ : EquivRel X), effectiveEquivRel ρ

class ArithmeticUniverse extends Recursive C, ListArithmetic C, Exact C

/-
...
1.defien the permutation on lists.
relationas
2. show that it is an equivalece relation.
-/

variable {C}

def perm [Recursive C] [HasPullbacks C] [ListArithmetic C] (X : C) :
    EquivRel (list X) := sorry
  -- R := _
  -- left := _
  -- right := _
  -- jointly_monic := _
  -- reflexive := _
  -- symmetric := _
  -- transitive := _

instance hasCoEq [ArithmeticUniverse C] (X : C) :
  HasCoequalizer (perm X).left (perm X).right := sorry

-- TODO: fix the universe variables.
--noncomputable
def bag [ArithmeticUniverse C] (X : C) : C :=
  coequalizer (perm X).left (perm X).right

-- TODO 1 : prove that bag is the free commutaive monoid internally in C.

-- TODO 2 : show that any internal commutative monoid structure
-- is equivalent to the data of an aggregator.

-- Use 1 and 2 to extract an aggregator for bags in ArithmeticUniverse C.

-- compose the aggregator and the oplus map to construct

-- define the horizontal map p⊗ similarly.

-- compose all the maps.









#moogle "internal relations in categories."
