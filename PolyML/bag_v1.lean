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

variable [HasPullbacks C] {A B C' : C} (f : A ⟶ B)
    (g : B ⟶ C')

def Kgg := pullback g g
def Khh := pullback (f ≫ g) (f ≫ g)

/-
Borceux - Lemma 2.1.2 :
Given a regular epimorphism `f : A ⟶ B`
and an arbitrary morphism `g : B ⟶ C`,
the induced map ` f ×C f : A ×c A ⟶ B ×c B`
is an epimorphism.
-/
def fxf : Khh f g ⟶ Kgg g := by
    let h := (pullback.fst (f ≫ g) (f ≫ g) ≫ f)
    let k := (pullback.snd (f ≫ g) (f ≫ g) ≫ f)
    have : IsPullback (pullback.fst g g) (pullback.snd g g) g g :=
      IsPullback.of_hasPullback g g
    apply CategoryTheory.IsPullback.lift this h k
    change (pullback.fst (f ≫ g) (f ≫ g) ≫ f) ≫ g =
      (pullback.snd (f ≫ g) (f ≫ g) ≫ f) ≫ g
    simp only [assoc]
    exact pullback.condition

def Kl := pullback f (pullback.fst g g)
def Kr := pullback f (pullback.snd g g)

def PullbackPr2Kl := pullback.snd f (pullback.fst g g)
def PullbackPr2Kr := pullback.snd f (pullback.snd g g)


variable [RegularEpi f]

def is_regular_epi_left [Regular C] :
  RegularEpi (PullbackPr2Kl f g) := by
  apply Regular.pullback_stability
  infer_instance

def is_regular_epi_right [Regular C] :
  RegularEpi (pullback.snd f (pullback.snd g g)) := by
  apply Regular.pullback_stability
  infer_instance

def map_to_pullback_left :
  Khh f g ⟶ Kl f g := by {
  apply CategoryTheory.IsPullback.lift ?_ (pullback.fst (f ≫ g) (f ≫ g)) (fxf f g)
  have : (fxf f g) ≫ (pullback.fst g g) = (pullback.fst (f ≫ g) (f ≫ g)) ≫ f := by {
    unfold fxf
    simp only [IsPullback.lift_fst]}
  apply this.symm
  · exact pullback.fst f (pullback.fst g g)
  · exact PullbackPr2Kl f g
  exact IsPullback.of_hasPullback f (pullback.fst g g)}

def map_to_pullback_right :
  Khh f g ⟶ Kr f g := by {
  apply CategoryTheory.IsPullback.lift ?_ (pullback.snd (f ≫ g) (f ≫ g)) (fxf f g)
  have : (fxf f g) ≫ (pullback.snd g g) = (pullback.snd (f ≫ g) (f ≫ g)) ≫ f := by {
    unfold fxf
    simp only [IsPullback.lift_snd]}
  apply this.symm
  · unfold Kr
    exact pullback.fst f (pullback.snd g g)
  · exact pullback.snd f (pullback.snd g g)
  exact IsPullback.of_hasPullback f (pullback.snd g g)}

def map_to_pullback_sqr : map_to_pullback_left f g ≫ (PullbackPr2Kl f g) =
   map_to_pullback_right f g ≫ pullback.snd f (pullback.snd g g) := by {
    unfold map_to_pullback_left map_to_pullback_right
    simp only [IsPullback.lift_snd, id_eq]}


variable {w : C} (k₁ : w ⟶ Kl f g) (k₂ : w ⟶ Kr f g)
 (IsPullbacketc : k₁ ≫ (PullbackPr2Kl f g) = k₂ ≫
    pullback.snd f (pullback.snd g g))

include IsPullbacketc
lemma is_pullback_sqr_mor_eq :
  (k₁ ≫ pullback.fst f (pullback.fst g g)) ≫ (f ≫ g) =
  (k₂ ≫ pullback.fst f (pullback.snd g g)) ≫ (f ≫ g) := by {
    unfold Kl at *
    unfold Kr at *
    rw [assoc]
    rw [assoc]
    have PullbackSqrCommutesKl : pullback.fst f (pullback.fst g g) ≫ f =
      (PullbackPr2Kl f g) ≫ (pullback.fst g g) :=
      pullback.condition
    have PullbackSqrCommutesKr : pullback.fst f (pullback.snd g g) ≫ f
     = pullback.snd f (pullback.snd g g) ≫ (pullback.snd g g)  :=
      pullback.condition
    have h1 : k₂ ≫ pullback.fst f (pullback.snd g g) ≫ f ≫ g =
     k₂ ≫ (pullback.fst f (pullback.snd g g) ≫ f) ≫ g :=
       by {simp only [assoc]}
    rw [h1]
    have h11 : k₁ ≫ pullback.fst f (pullback.fst g g) ≫ f ≫ g =
      k₁ ≫ (pullback.fst f (pullback.fst g g) ≫ f) ≫ g := by {
        simp only [assoc]
      }
    rw [h11]
    rw [PullbackSqrCommutesKl]
    rw [PullbackSqrCommutesKr]
    have : k₁ ≫ (PullbackPr2Kl f g ≫ pullback.fst g g) ≫ g =
      (k₁ ≫ (PullbackPr2Kl f g)) ≫ pullback.fst g g ≫ g := by {
        simp only [assoc]
      }
    rw [this]
    have :  k₂ ≫ (pullback.snd f (pullback.snd g g)
      ≫ pullback.snd g g) ≫ g =
      (k₂ ≫ (pullback.snd f (pullback.snd g g)
      ≫ pullback.snd g g)) ≫ g := by {simp only [assoc]}
    rw [this]
    rw [IsPullbacketc]
    have PullbackSqrCommutes : pullback.fst g g ≫ g =
      pullback.snd g g ≫ g := pullback.condition
    rw [PullbackSqrCommutes]
    simp only [assoc]
  }

def is_pullback_sqr_mor : w ⟶ Khh f g:= by {
  unfold Khh
  apply CategoryTheory.IsPullback.lift ?_
    (k₁ ≫ pullback.fst f (pullback.fst g g))
    (k₂ ≫ pullback.fst f (pullback.snd g g))
  apply is_pullback_sqr_mor_eq f g k₁ k₂ (IsPullbacketc)
  · exact pullback.fst (f ≫ g) (f ≫ g)
  · exact pullback.snd (f ≫ g) (f ≫ g)
  · exact IsPullback.of_hasPullback (f ≫ g) (f ≫ g)}

lemma is_pullback_sqr_mor_pr1 :
  is_pullback_sqr_mor f g k₁ k₂ (IsPullbacketc) ≫
  map_to_pullback_left f g = k₁ := by {
  unfold is_pullback_sqr_mor map_to_pullback_left
  unfold fxf
  simp only
  have PullbackSqrCommutesKl : pullback.fst f (pullback.fst g g) ≫ f =
    (PullbackPr2Kl f g) ≫ (pullback.fst g g) :=
    pullback.condition
  have PullbackSqrCommutesKr : pullback.fst f (pullback.snd g g) ≫ f
    = pullback.snd f (pullback.snd g g) ≫ (pullback.snd g g)  :=
    pullback.condition
  unfold PullbackPr2Kl at *
  apply CategoryTheory.Limits.pullback.hom_ext
  · simp only [id_eq, assoc, IsPullback.lift_fst]
  · simp only [id_eq]
    apply CategoryTheory.Limits.pullback.hom_ext
    · have : (k₁ ≫ pullback.snd f (pullback.fst g g)) ≫ pullback.fst g g=
        k₁ ≫ (pullback.snd f (pullback.fst g g)) ≫ pullback.fst g g := by {
          simp only [assoc]
        }
      rw [this]
      rw [← PullbackSqrCommutesKl]
      simp only [assoc, IsPullback.lift_snd,
        IsPullback.lift_fst, IsPullback.lift_fst_assoc]
    · simp only [assoc, IsPullback.lift_snd, IsPullback.lift_snd_assoc]
      have : k₂ ≫ pullback.fst f (pullback.snd g g) ≫ f =
        k₂ ≫ (pullback.fst f (pullback.snd g g) ≫ f) := by {
          simp only [assoc]
        }
      rw [this]
      rw [PullbackSqrCommutesKr]
      have : k₂ ≫ pullback.snd f (pullback.snd g g) ≫ pullback.snd g g=
       (k₂ ≫ pullback.snd f (pullback.snd g g)) ≫ pullback.snd g g := by {
        simp only [assoc]
       }
      rw [this, ← (IsPullbacketc)]
      simp only [assoc]
}


lemma is_pullback_sqr_mor_pr2 :
  is_pullback_sqr_mor f g k₁ k₂ (IsPullbacketc) ≫
  map_to_pullback_right f g = k₂ := by {
  unfold is_pullback_sqr_mor map_to_pullback_right
  have PullbackSqrCommutesKl : pullback.fst f (pullback.fst g g) ≫ f =
    (PullbackPr2Kl f g) ≫ (pullback.fst g g) :=
    pullback.condition
  have PullbackSqrCommutesKr : pullback.fst f (pullback.snd g g) ≫ f
      = pullback.snd f (pullback.snd g g) ≫ (pullback.snd g g)  :=
     pullback.condition
  unfold PullbackPr2Kl fxf at *
  apply CategoryTheory.Limits.pullback.hom_ext
  · simp only [id_eq, assoc, IsPullback.lift_fst, IsPullback.lift_snd]
  · simp only [id_eq]
    apply CategoryTheory.Limits.pullback.hom_ext
    · simp only [assoc, IsPullback.lift_snd, IsPullback.lift_fst,
        IsPullback.lift_fst_assoc]
      have :  k₁ ≫ pullback.fst f (pullback.fst g g) ≫ f =
         k₁ ≫ (pullback.fst f (pullback.fst g g) ≫ f) := by {
          simp only [assoc]
         }
      rw [this]
      rw [PullbackSqrCommutesKl]
      have : k₁ ≫ pullback.snd f (pullback.fst g g) ≫ pullback.fst g g =
        (k₁ ≫ pullback.snd f (pullback.fst g g)) ≫ pullback.fst g g := by {
          simp only [assoc]
        }
      rw [this, (IsPullbacketc)]
      simp only [assoc]
    · simp only [assoc, IsPullback.lift_snd, IsPullback.lift_snd_assoc]
      rw [PullbackSqrCommutesKr]}

def is_pullback_sqr_unique  :
  ∃! hk, (hk ≫ (map_to_pullback_left f g ) = k₁ ∧
    hk ≫ map_to_pullback_right f g = k₂) := sorry

#check map_to_pullback_sqr

def is_pullback_sqr : IsPullback (map_to_pullback_left f g)
 (map_to_pullback_right f g)
 (PullbackPr2Kl f g) (pullback.snd f (pullback.snd g g)) := by {
  constructor
  · have := (is_pullback_sqr_unique f g k₁ k₂).choose
    sorry
  · constructor
    exact map_to_pullback_sqr f g
 }

def pullback_map_regular_epi [HasPullbacks C] [Regular C]
  {A B C' : C} (f : A ⟶ B) (g : B ⟶ C') [RegularEpi f] :
  Epi (fxf f g) := by {
    have PullbackSqrCommutesKr : pullback.fst f (pullback.snd g g) ≫ f
      = pullback.snd f (pullback.snd g g) ≫ (pullback.snd g g)  :=
     pullback.condition
    let q : Khh f g ⟶ Kr f g := map_to_pullback_right f g
    let t := PullbackPr2Kr f g
    have Hq : fxf f g =  q ≫ t :=  by {
      unfold fxf q t
      unfold map_to_pullback_right
      unfold PullbackPr2Kr
      unfold fxf
      simp only [id_eq, IsPullback.lift_snd]
    }
    rw [Hq]
    haveI : Epi t := by {
      unfold t
      unfold PullbackPr2Kr
      have : RegularEpi (pullback.snd f (pullback.snd g g)) := by {
        apply is_regular_epi_right f g
      }
      apply RegularEpi.epi
    }
    haveI : Epi q := by {
      have : RegularEpi q := by {
        unfold q
        unfold map_to_pullback_right
        simp only [id_eq]
        have :=is_regular_epi_left f g
        unfold PullbackPr2Kl at this
        unfold fxf
        simp only
        sorry
      }
      apply RegularEpi.epi
    }
    apply epi_comp

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
    have := pullback_map_regular_epi F.ι F.π
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

--strongEpi_of_regularEpi
--Borceux Prop. 2.14 In a regular category, the following conditions
--are equivalent (1) f is a regular epi (2) f is a strong epi.
def regular_epi_iff_strong_epi {X Y : C} (f : X ⟶ Y) [Regular C] [H : StrongEpi f] :
  RegularEpi f := by
    have Hepi : Epi f := H.epi
    have Hllp : ∀ ⦃X Y : C⦄ (z : X ⟶ Y) [Mono z], HasLiftingProperty f z := H.llp
    let F := (regular_epi_mono_factorisation (A:= X) (A' := Y) f).choose
    have HF := (regular_epi_mono_factorisation (A:= X) (A' := Y) f).choose_spec
    sorry



#exit

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
