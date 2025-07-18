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

#check HasFiniteLimits C

#check IsKernelPair

#check CategoryTheory.IsKernelPair

#moogle "Coequalizer."

#moogle "Coequalizer universal property."

#check CategoryTheory.RegularEpi

#check CategoryTheory.Preregular

namespace RegularEpi


def effectiveEpiStructOfRegularEpi' {B X : C} (f : X ⟶ B) [RegularEpi f] :
    EffectiveEpiStruct f where
  desc e h := Cofork.IsColimit.desc isColimit e (h left right w)
  fac _ _ := Cofork.IsColimit.π_desc' isColimit _ _
  uniq _ _ _ hg := Cofork.IsColimit.hom_ext isColimit (hg.trans
    (Cofork.IsColimit.π_desc' _ _ _).symm)


/-- A regular category is a category with finite limits where equalisers of kernel pairs exist, and regular epimorphisms (=effective epis) are stable under pullbacks. -/
class Regular extends HasFiniteLimits C where
  equiv_rel_coeq : ∀ {W X Y : C} (f : X ⟶ Y) (a b : W ⟶ X),
    IsKernelPair f a b → HasCoequalizer a b
  pullback_stability : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z),
    RegularEpi f → RegularEpi (pullback.snd f g)

/-- Every regular category is preregular. -/
def Regular.toPreregular [Regular C] : Preregular C where
  exists_fac {X Y Z} f g w := by
    use pullback g f, pullback.snd g f
    let h_reg := pullback_stability g f (regularEpiOfEffectiveEpi g)
    have : EffectiveEpi (pullback.snd g f) := by
      infer_instance
    use this, pullback.fst g f
    exact pullback.condition


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
