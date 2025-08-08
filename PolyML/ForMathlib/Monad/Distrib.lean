/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib
import PolyML.FreeCommMon

/-
There is no reason any two monads `S` and `T` on the same category can be composed to give
a new monad. The obstacle is forming the multiplication; though we can construct
`TTSS ⥤ TS` and `SSTT ⥤ ST`, we cannot construct a natural isomorphism `TSTS ⥤ TS` in general.

However this is possible when there is a so-called distributive law
between them, i.e. a natural transformation `δ : ST ⥤ TS`, satisfying certain axioms. In this case,
the functor `TS` is a monad, and the natural transformation `δ` is used to define the multiplication of the new monad.

We say the monad `s` distributes over the monad `T` if there is a natural transformation `δ : ST ⥤ TS` compatible with
the units and multiplications of the two monads. The natural transformation `δ` is referred to as a distributive law.

In the presence of a distributive law, the underlying functor of the composition of the two monads
is given the the composition of their respective underlying functors, and in fact, the the composition of two
monads `S` and `T` is then defined as `⟨S ⋙ T, S.η ≫ T·η, TλS ≫ S.μ  ⟩`.
-/

universe u v

namespace CategoryTheory

open Category MonoidalCategory Endofunctor Functor

variable {C : Type u} [Category.{v} C]

attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

namespace Monad

class DistribLaw (S T : Monad C) where
  δ : T.1 ⊗ S.1 ⟶ S.1 ⊗ T.1
  unit_left : T.η ▷ S.1 ≫ δ = S.1 ◁ T.η
  unit_right : T.1 ◁ S.η ≫ δ = S.η ▷ T.1
  mul_left :  T.1 ◁ δ ≫ δ ▷ T.1 ≫ S.1 ◁ T.μ = T.μ ▷ S.1 ≫ δ
  mul_right : δ ▷ S.1 ≫ S.1 ◁ δ ≫ S.μ ▷ T.1 = T.1 ◁ S.μ ≫ δ

namespace DistribLaw

#check CategoryTheory.RelCat

#check CategoryTheory.Endofunctor.Algebra

/- If `S` distributes over `T`, `T` maps algebras of `S` to algebras of `S`. -/
def liftToMonadAlgebra (S T : Monad C) [DistribLaw S T] (α : S.Algebra) : S.Algebra where
  A := T.obj α.A
  a := DistribLaw.δ.app α.A ≫ T.map α.a
  unit := by {
    have hl := DistribLaw.unit_left (S := S) (T := T)
    have hr := DistribLaw.unit_right (S := S) (T := T)
    --have hassocS := Monad.assoc S α.A
    have hassocT := Monad.assoc T α.A
    --have hunitS := Monad.left_unit S α.A
    have hunitT := Monad.left_unit T α.A
    have hunitSr := Monad.right_unit S α.A
    have hunitTr := Monad.right_unit T α.A
    have H1T := Monad.unit_naturality C T
    --have H1S := Monad.unit_naturality C S
    --have H2S := Monad.mu_naturality C S
    have H2T := Monad.mu_naturality C T
    let f := S.η.app (T.obj α.A)
    let g:= T.map (T.η.app α.A)
    simp only [Functor.id_obj] at *
    rw [← hunitTr]
    have := H2T g
    simp only [endofunctorMonoidalCategory_tensorObj_obj]
    sorry


    --rw [H2T]
    --have := H1T







  }
  assoc := by {
    have hassocS := Monad.assoc S α.A
    have hassocT := Monad.assoc T α.A
    simp only [comp_obj, endofunctorMonoidalCategory_tensorObj_obj, map_comp, Category.assoc]


  }

@[reassoc (attr := simp)]
theorem liftToMonadAlgebra_str {S T : Monad C} [DistribLaw S T] {α : S.Algebra} :
    (liftToMonadAlgebra S T α).a = DistribLaw.δ.app α.A ≫ T.map α.a := by
  rfl

theorem distrib_naturality {S T : Monad C} [DistribLaw S T] {X Y : C} (f : X ⟶ Y) :
    S.map (T.map f) ≫ δ.app Y = δ.app X ≫ T.map (S.map f) :=
  δ.naturality f

/-- If `S` distributes over `T`, the monad `T` lifts to an endofucntor on the category of algebras of `S`. -/
def liftToMonadAlgebraEndoFunctor (S T : Monad C) [DistribLaw S T] : S.Algebra ⥤ S.Algebra where
  obj := liftToMonadAlgebra S T
  map {α β} g := {
    f := T.map g.f
    h := by
      rw [liftToMonadAlgebra_str]
      rw [reassoc_of% (distrib_naturality g.f), ← map_comp, g.h, map_comp, ← Category.assoc]
      simp only [liftToMonadAlgebra_str]
  }
  map_id := by aesop_cat
  map_comp := by aesop_cat

theorem liftToMonadAlgebraEndoFunctor_forget {S T : Monad C} [DistribLaw S T] :
    liftToMonadAlgebraEndoFunctor S T ⋙ S.forget = S.forget ⋙ T.1 := by
  rfl

/-- If `S` distributes over `T` then `T` lifts to monad on the category of algebras of `S`. -/
def liftToMonadAlgebraMonad {S T : Monad C} [DistribLaw S T] : Monad S.Algebra :=
  { liftToMonadAlgebraEndoFunctor S T with
    η := sorry,
    μ := sorry,
    assoc := sorry,
    left_unit := sorry,
    right_unit := sorry}

end DistribLaw

instance [CartesianMonoidalCategory C] [ListArithmetic C] [WithBags C] :
    DistribLaw (list.monad C) (bag.monad C) where
  δ := {
    app X := sorry
    naturality := sorry
  }
  unit_left := sorry
  unit_right := sorry
  mul_left := sorry
  mul_right := sorry




end Monad

end CategoryTheory
