import PolyML.ListArithmetic
import Mathlib

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

class Regular extends HasFiniteLimits C where
  equiv_rel_coeq : ∀ {W X Y : C} (f : X ⟶ Y) (a b : W ⟶ X),
    IsKernelPair f a b → HasCoequalizer a b
  pullback_stability : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z),
    RegularEpi f → RegularEpi (pullback.snd f g)

#check Regular

#check CategoryTheory.Factorisation

#check CategoryTheory.Limits.coequalizer.desc'

variable {C}

structure RegularEpiFactorisation {X Y : C} (f : X ⟶ Y)
    extends Factorisation f where
  regular_epi : RegularEpi ι

-- a good test for the definition.
-- ref: 8.3. Proposition of Barrs and Wells
-- In a regular category, every morphism `f : X ⟶ Y`
-- can be factored as `f = m ≫ e`,
-- where `e` is a regular epimorphism and `m` is a monomorphism.

def regularEpiFactorization {A A' : C} [Regular C] (f : A ⟶ A') :
  RegularEpiFactorisation f where
    mid := by {
      let K := pullback f f
      let d0 : K ⟶ A := pullback.fst f f
      let d1 : K ⟶ A := pullback.snd f f
      haveI kernelPair : IsKernelPair f d0 d1 :=
        IsPullback.of_hasPullback f f
      haveI := Regular.equiv_rel_coeq f d0 d1 kernelPair
      exact coequalizer d0 d1}
    ι := by {
      let K := pullback f f
      let d0 : K ⟶ A := pullback.fst f f
      let d1 : K ⟶ A := pullback.snd f f
      haveI kernelPair : IsKernelPair f d0 d1 :=
        IsPullback.of_hasPullback f f
      haveI := Regular.equiv_rel_coeq f d0 d1 kernelPair
      -- let g be the coequalizer of d0 and d1.
      let g : A ⟶ coequalizer d0 d1 := coequalizer.π d0 d1
      exact g
    }
    π := by {
      let K := pullback f f
      let d0 : K ⟶ A := pullback.fst f f
      let d1 : K ⟶ A := pullback.snd f f
      haveI kernelPair : IsKernelPair f d0 d1 :=
        IsPullback.of_hasPullback f f
      haveI := Regular.equiv_rel_coeq f d0 d1 kernelPair
      apply CategoryTheory.Limits.coequalizer.desc f
      exact pullback.condition}
    ι_π := by {
      simp only [colimit.ι_desc, Cofork.ofπ_pt, Cofork.ofπ_ι_app] }
    regular_epi := by {
      let K := pullback f f
      let d0 : K ⟶ A := pullback.fst f f
      let d1 : K ⟶ A := pullback.snd f f
      haveI kernelPair : IsKernelPair f d0 d1 := IsPullback.of_hasPullback f f
      haveI := Regular.equiv_rel_coeq f d0 d1 kernelPair
      let g : A ⟶ coequalizer d0 d1 := coequalizer.π d0 d1
      simp only
      constructor
      exact coequalizerIsCoequalizer (pullback.fst f f) (pullback.snd f f)
    }



theorem regular_epi_mono_factorisation {A A' : C} [Regular C] (f : A ⟶ A'):
  ∃ (F : RegularEpiFactorisation f), Mono F.π := by
  let F := regularEpiFactorization f
  exact ⟨F, by
    -- provide the proof that F.π is mono
    constructor
    intros Z e0 e1 he0e1
    let Kh := pullback F.ι F.ι
    let d0 : Kh ⟶ A := pullback.fst F.ι F.ι
    let d1 : Kh ⟶ A := pullback.snd F.ι F.ι
    sorry

⟩

#check Quot

#check WalkingParallelPair

/-
define internal relations in categories. more or
less following definition 6 of Carboni-Vitale.
Def 2.4.2 of Mathis Menni's thesis
-/
structure EquivRel (X : C) where
  R : C
  (left right : R ⟶ X)
  jointly_monic : Mono (prod.lift left right)
  reflexive : sorry
  symmetric : sorry
  transitive : sorry

def effectiveEquivRel {X : C} (ρ : EquivRel X) :=
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

def perm [Recursive C] [ListArithmetic C] (X : C) : EquivRel (list X) where
  R := _
  left := _
  right := _
  jointly_monic := _
  reflexive := _
  symmetric := _
  transitive := _

instance hasCoEq [ArithmeticUniverse C] (X : C) :
  HasCoequalizer (perm X).left (perm X).right := sorry

-- TODO: fix the universe variables.
--noncomputable
def bag [ArithmeticUniverse C] (X : C) : C :=
  coequalizer (perm X).left (perm X).right

-- TODO 1 : prove that bag is the free commutaive monoid internally in C.

-- TODO 2 : show that any internal commutative monoid structure
-- is equivalent to the data of an aggregator.

-- Use 1 and 2 to extract an aggregotor for bags in ArithmeticUniverse C.

-- compose the aggregator and the oplus map to construct

-- define the horizontal map p⊗ similarly.

-- compose all the maps.









#moogle "internal relations in categories."

#check CategoryTheory.rel
