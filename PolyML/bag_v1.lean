import PolyML.ListArithmetic
import Mathlib

universe u v

noncomputable section
namespace CategoryTheory

open Functor Opposite Limits MonoidalCategory CartesianMonoidalCategory Recursive ListArithmetic Category

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

open Endofunctor Algebra

variable (U : C)

#check HasFiniteLimits C

#check IsKernelPair

#check CategoryTheory.IsKernelPair

#moogle "Coequalizer."

#check CategoryTheory.RegularEpi

class Regular extends HasFiniteLimits C where
  equiv_rel_coeq : ∀ {W X Y : C} (f : X ⟶ Y) (a b : W ⟶ X),
    IsKernelPair f a b → HasCoequalizer a b
  pullback_stability : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z),
    RegularEpi f → RegularEpi (pullback.snd f g)


#check CategoryTheory.Factorisation


structure RegularEpiFactorisation {X Y : C} (f : X ⟶ Y) extends Factorisation f where
  regular_epi : RegularEpi ι

/-- a good test for the definition.
ref: 8.3. Proposition of Barrs and Wells

-/
def regularEpiFactorization {X Y : C} (f : X ⟶ Y) : RegularEpiFactorisation f := sorry

#check Quot

#check WalkingParallelPair

/-
define internal relations in categories. more or less following definition 6 of Carboni-Vitale.
Def 2.4.2 of Mathis Menni's thesis
-/
structure Rel (X : C) where
  R : C
  (left right : R ⟶ X)
  jointly_monic : Mono (prod.lift left right)
  reflexive : sorry
  symmetric : sorry
  transitive : sorry


/-
...
1.defien the permutation on lists.
relationas
2. show that it is an equivalece relation.
-/

def perm [Recursive C] [ListArithmetic C] (X : C) : Rel (list X) where
  R := _
  left := _
  right := _
  jointly_monic := _
  reflexive := _
  symmetric := _
  transitive := _


#moogle "internal relations in categories."

#check CategoryTheory.rel
