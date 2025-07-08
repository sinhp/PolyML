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
-- can be factored as `f = e ≫ m`,
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
      exact coequalizerIsCoequalizer (pullback.fst f f) (pullback.snd f f)}

/-
Borceux : Lemma 2.1.2 :
Given a regular epimorphism `f : A ⟶ B` and an arbitrary morphism `g : B ⟶ C`,
the induced map `prod.map f f : A × A ⟶ B × B` is a regular epimorphism.
-/
def prod_map_regular_epi [HasPullbacks C]
  {A B C' : C} (f : A ⟶ B) (g : B ⟶ C') [RegularEpi f] :
    Epi (prod.map f f) where
      left_cancellation := by {
        intros Z g h hgh
        have BxB := pullback g g
        let e : B ⨯ A ⟶ B ⨯ A := 𝟙 (B ⨯ A)
        let h : B ⨯ A ⟶ A := prod.snd
        let a : B ⨯ A ⟶ B := prod.fst
        let c : A ⨯ B ⟶ A := prod.fst
        let j : A ⨯ A ⟶ B ⨯ A := sorry
        let i : A ⨯ A ⟶ A ⨯ B := sorry
        let d : A ⨯ B ⟶ B ⨯ A := sorry
        sorry



      }

#check Mono
theorem regular_epi_mono_factorisation {A A' : C}
    [Regular C] (f : A ⟶ B):
  ∃ (F : RegularEpiFactorisation f), Mono F.π := by
  let F := regularEpiFactorization f
  exact ⟨F, by
    -- provide the proof that F.π is mono
    constructor
    intros Z e0 e1 he0e1
    have := CommSq.mk he0e1
    have := F.ι_π

    let P := pullback f f
    let u : P ⟶ A := pullback.fst f f
    let v : P ⟶ A := pullback.snd f f

    let R := pullback F.π F.π
    let r : R ⟶ F.mid := pullback.fst F.π F.π
    let s : R ⟶ F.mid := pullback.snd F.π F.π
    have : RegularEpi F.ι := F.regular_epi
    have := prod_map_regular_epi F.ι F.π
    --have : Epi F.ι := StrongEpi.epi
    have h1 : (u ≫ F.ι) ≫ F.π = (v ≫ F.ι) ≫ F.π := by {
      simp only [assoc, Factorisation.ι_π]
      exact pullback.condition
    }
    let q : P ⟶ R := pullback.lift (u ≫ F.ι) (v ≫ F.ι) h1
    let q' := pullback.lift e0 e1 he0e1
    have sq1 : CommSq u q F.ι r := by
      simp_all only [limit.lift_π, PullbackCone.mk_pt,
      PullbackCone.mk_π_app,
      CommSq.mk, F, P, R, u, q, v, r]
    have sq1' : CommSq u q F.ι s := sorry
    have sq2 : CommSq v q F.ι r := sorry
    have sq2' : CommSq v q F.ι s := by
      simp_all only [limit.lift_π, PullbackCone.mk_pt,
      PullbackCone.mk_π_app,
      CommSq.mk, F, R, P, r, v, u, q, s]
    sorry










        -- have hrq : q ≫ r = u ≫ F.ι := by {sorry
    --   }
    -- have hrq : u ≫ F.ι = v ≫ F.ι := by {sorry
    --   }


    --have :=  this.left_cancellation r s
⟩

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

def perm [Recursive C] [HasPullbacks C] [ListArithmetic C] (X : C) : EquivRel (list X) where
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

-- Use 1 and 2 to extract an aggregator for bags in ArithmeticUniverse C.

-- compose the aggregator and the oplus map to construct

-- define the horizontal map p⊗ similarly.

-- compose all the maps.









#moogle "internal relations in categories."

#check CategoryTheory.rel
