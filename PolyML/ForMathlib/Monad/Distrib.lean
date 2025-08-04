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


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory Endofunctor Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₂} D]


attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

namespace Monad

class DistribLaw (S T : Monad C) where
  δ : T.1 ⊗ S.1 ⟶ S.1 ⊗ T.1
  unit_left : T.η ▷ S.1 ≫ δ = S.1 ◁ T.η
  unit_right : T.1 ◁ S.η ≫ δ = S.η ▷ T.1
  mul_left :  T.1 ◁ δ ≫ δ ▷ T.1 ≫ S.1 ◁ T.μ = T.μ ▷ S.1 ≫ δ
  mul_right : δ ▷ S.1 ≫ S.1 ◁ δ ≫ S.μ ▷ T.1 = T.1 ◁ S.μ ≫ δ


namespace DistribLaw

theorem distrib_naturality {S T : Monad C} [DistribLaw S T] {X Y : C} (f : X ⟶ Y) :
    S.map (T.map f) ≫ δ.app Y = δ.app X ≫ T.map (S.map f) :=
  δ.naturality f

end DistribLaw

class Lift (S T : Monad C) extends Monad (S.Algebra) where
  w : toFunctor ⋙ S.forget = S.forget ⋙ T.1
  respect_unit : whiskerRight η S.forget ≫ eqToHom w = whiskerLeft S.forget T.η
  respect_mul : whiskerRight μ S.forget ≫ eqToHom w = eqToHom (by rw [Functor.assoc, w, ← Functor.assoc, w, Functor.assoc]) ≫ whiskerLeft S.forget T.μ


namespace Lifting

open DistribLaw

variable {S : Monad C}

/- If `S` distributes over `T`, `T` maps algebras of `S` to algebras of `S`. -/
def map (T : Monad C) [DistribLaw S T] (α : S.Algebra) : S.Algebra where
  A := T.obj α.A
  a := DistribLaw.δ.app α.A ≫ T.map α.a
  unit := sorry
  assoc := sorry

@[reassoc (attr := simp)]
theorem map_str {T : Monad C} [DistribLaw S T] {α : S.Algebra} :
    (map T α).a = DistribLaw.δ.app α.A ≫ T.map α.a := by
  rfl

/-- If `S` distributes over `T`, the monad `T` lifts to an endofucntor on the category of algebras of `S`. -/
def endoFunctor (T : Monad C) [DistribLaw S T] : S.Algebra ⥤ S.Algebra where
  obj := map T
  map {α β} g := {
    f := T.map g.f
    h := by
      rw [map_str]
      rw [reassoc_of% (distrib_naturality g.f), ← map_comp, g.h, map_comp, ← Category.assoc]
      simp only [map_str]
  }

/-- If `S` distributes over `T` then `T` lifts to monad on the category of algebras of `S`. -/
def monad (T : Monad C) [DistribLaw S T] : Monad S.Algebra where
  toFunctor := endoFunctor T
  η := sorry
  μ := sorry
  assoc := sorry
  left_unit := sorry
  right_unit := sorry

instance {T : Monad C} [DistribLaw S T] : Lift S T where
  toMonad := monad T
  w := rfl
  respect_unit := sorry
  respect_mul := sorry

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

end Lifting

open DistribLaw

@[simp]
theorem unit_exchange {S T : Monad C} : S.η ≫ (S.1 ◁ T.η) = T.η ≫ (S.η ▷ T.1) := by
  ext X
  exact T.η.naturality <| S.η.app X

#check NatTrans.hcomp

@[simps]
def comp (S T : Monad C) [DistribLaw S T] : Monad C where
  toFunctor := S.toFunctor ⋙ T.toFunctor
  η := S.η ≫ (S.1 ◁ T.η)
  μ := by
    let w := S.μ ⊗ₘ T.μ
    exact (S.1 ◁ δ ▷ T.1) ≫ w
  assoc := sorry
  left_unit := sorry
  right_unit := sorry

theorem comp_unit {S T : Monad C} [DistribLaw S T] : (comp S T).η = T.η ≫ (S.η ▷ T.1) := by
  simp only [comp_η, unit_exchange]










end Monad

end CategoryTheory
