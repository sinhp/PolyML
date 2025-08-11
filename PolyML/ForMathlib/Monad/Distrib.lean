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
set_option linter.simpsNoConstructor false

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory Endofunctor Functor Recursive

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₂} D]

attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

namespace Monad

class DistribLaw (S T : Monad C) where
  δ : T.1 ⊗ S.1 ⟶ S.1 ⊗ T.1
  unit_left : T.η ▷ S.1 ≫ δ = S.1 ◁ T.η
  unit_right : T.1 ◁ S.η ≫ δ = S.η ▷ T.1
  mul_left :  T.1 ◁ δ ≫ δ ▷ T.1 ≫ S.1 ◁ T.μ = T.μ ▷ S.1 ≫ δ
  mul_right : δ ▷ S.1 ≫ S.1 ◁ δ ≫ S.μ ▷ T.1 = T.1 ◁ S.μ ≫ δ

attribute [reassoc (attr := simp)] DistribLaw.unit_left DistribLaw.unit_right DistribLaw.mul_left DistribLaw.mul_right

namespace DistribLaw

variable {S T : Monad C} [DistribLaw S T]

theorem distrib_naturality {X Y : C} (f : X ⟶ Y) :
    S.map (T.map f) ≫ δ.app Y = δ.app X ≫ T.map (S.map f) :=
  δ.naturality f

@[reassoc (attr := simp)]
theorem unit_left_components {X : C} : S.map (T.η.app X) ≫ δ.app X = T.η.app (S.obj X) :=
  NatTrans.congr_app unit_left X

@[reassoc (attr := simp)]
theorem unit_right_components {X : C} : S.η.app (T.obj X) ≫ δ.app X = T.map (S.η.app X) :=
  NatTrans.congr_app unit_right X

@[reassoc (attr := simp)]
theorem mul_left_components {X : C} :
    δ.app (T.obj X) ≫ T.map (δ.app X) ≫ T.μ.app (S.obj X) = S.map (T.μ.app X) ≫ δ.app X :=
  NatTrans.congr_app mul_left X

@[reassoc (attr := simp)]
theorem mul_right_components {X : C} :
    S.map (δ.app X) ≫ δ.app (S.obj X) ≫ T.map (S.μ.app X) = S.μ.app (T.obj X) ≫ δ.app X :=
  NatTrans.congr_app mul_right X

end DistribLaw

class Lift (S T : Monad C) extends Monad (S.Algebra) where
  w : toFunctor ⋙ S.forget = S.forget ⋙ T.1
  respect_unit : whiskerRight η S.forget ≫ eqToHom w = whiskerLeft S.forget T.η
  respect_mul : whiskerRight μ S.forget ≫ eqToHom w = eqToHom
    (by rw [Functor.assoc, w, ← Functor.assoc, w, Functor.assoc]) ≫ whiskerLeft S.forget T.μ

namespace LiftingMonad

open DistribLaw

variable {S : Monad C} (T : Monad C) [DistribLaw S T]

/- If `S` distributes over `T`, `T` maps algebras of `S` to algebras of `S`. -/
def map (α : S.Algebra) : S.Algebra where
  A := T.obj α.A
  a := DistribLaw.δ.app α.A ≫ T.map α.a
  unit := by simp only [unit_right_components_assoc, ← map_comp, α.unit, map_id]
  assoc := by
    rw [← Category.assoc,← mul_right_components]
    rw [Category.assoc, Category.assoc, ← map_comp, Algebra.assoc (C:=C) α]
    simp only [map_comp, Category.assoc]
    refine S.map (δ.app α.A) ≫= ?_
    rw [← Category.assoc, ← Category.assoc]
    refine ?_ =≫ T.map α.a
    exact _root_.id (Eq.symm (distrib_naturality (S:=S) (T:=T) (f:= α.a)))

@[reassoc (attr := simp)]
theorem map_str {T : Monad C} [DistribLaw S T] {α : S.Algebra} :
    (map T α).a = DistribLaw.δ.app α.A ≫ T.map α.a := by
  rfl

/-- If `S` distributes over `T`, the monad `T` lifts to an endofucntor on the category of algebras of `S`. -/
@[simps]
def endoFunctor : S.Algebra ⥤ S.Algebra where
  obj := map T
  map {α β} g := {
    f := T.map g.f
    h := by
      rw [map_str]
      rw [reassoc_of% (distrib_naturality g.f), ← map_comp, g.h, map_comp, ← Category.assoc]
      simp only [map_str]
  }

variable (S)

/-- If `S` distributes over `T` then `T` lifts to monad on the category of algebras of `S`. -/
def monad : Monad S.Algebra where
  toFunctor := endoFunctor T
  η := {
    app X := ⟨T.η.app X.A, by simp; erw [T.η.naturality X.a]⟩
    naturality α β f := by ext; apply Monad.unit_naturality}
  μ := {
    app X := ⟨T.μ.app X.A , by {
      simp only [comp_obj, endoFunctor_obj, map_str, endofunctorMonoidalCategory_tensorObj_obj,
        map_comp, Category.assoc]
      rw [← Category.assoc, ← mul_left_components]
      rw [Monad.mu_naturality (T:= T) (f:= X.a), ← Category.assoc, ← Category.assoc]
      exact Category.assoc
        (δ.app (T.obj X.A) ≫ T.map (δ.app X.A)) (T.μ.app (S.obj X.A)) (T.map X.a)
    }⟩
    naturality α β f := by ext; apply Monad.mu_naturality}
  assoc α := by ext; apply Monad.assoc
  left_unit α := by ext; apply Monad.left_unit
  right_unit α := by ext; apply Monad.right_unit

variable {S T}

def fstAlg (α : (monad S T).Algebra) : S.Algebra := α.A

def fstAlgFunctor : (monad S T).Algebra ⥤ S.Algebra where
  obj := fstAlg
  map {α β} g := {
    f := sorry
    h := sorry
  }

@[simps]
def sndAlg (α : (monad S T).Algebra) : T.Algebra where
  A := α.A.A
  a := α.a.f
  unit := by {sorry
  }
  assoc := sorry

@[reassoc (attr := simp)]
def distrib (α : (monad S T).Algebra) :
    δ.app (fstAlg α |>.A) ≫ T.map (fstAlg α).a ≫ (sndAlg α).a = S.map (sndAlg α).a ≫ (fstAlg α).a := by
  sorry

instance {T : Monad C} [DistribLaw S T] : Lift S T where
  toMonad := monad S T
  w := rfl
  respect_unit := by {
    simp only [eqToHom_refl, comp_id]
    rfl
  }
  respect_mul := by {
    simp only [eqToHom_refl, comp_id, id_comp]
    rfl
  }

end LiftingMonad

open DistribLaw

@[simp]
theorem unit_exchange {S T : Monad C} : S.η ≫ (S.1 ◁ T.η) = T.η ≫ (S.η ▷ T.1) := by
  ext X
  exact T.η.naturality <| S.η.app X

@[simps]
def comp (S T : Monad C) [DistribLaw S T] : Monad C where
  toFunctor := S.toFunctor ⋙ T.toFunctor
  η := S.η ≫ (S.1 ◁ T.η)
  μ := by
    let w := S.μ ⊗ₘ T.μ
    exact (S.1 ◁ δ ▷ T.1) ≫ w
  assoc X := by {
    simp only [comp_obj, NatTrans.comp_app,
      endofunctorMonoidalCategory_tensorObj_obj,
      endofunctorMonoidalCategory_whiskerLeft_app,
      endofunctorMonoidalCategory_whiskerRight_app,
      endofunctorMonoidalCategory_tensorMap_app,
      Functor.comp_map, map_comp, Category.assoc]
    have := Monad.mu_naturality (T:= T)
    stop





    rw [← Category.assoc]
    rw [← Category.assoc]
    rw [← map_comp]
    rw [Category.assoc]
    rw [← map_comp]
    rw [← Category.assoc]
    rw [← map_comp]
    have :   T.map (δ.app (S.obj (T.obj (S.obj X)))) ≫
    T.μ.app (S.obj (S.obj (T.obj (S.obj X)))) ≫
      T.map (S.μ.app (T.obj (S.obj X))) ≫ T.map (δ.app (S.obj X)) ≫
      T.μ.app (S.obj (S.obj X)) ≫ T.map (S.μ.app X)=
        T.map (δ.app (S.obj (T.obj (S.obj X)))) ≫
    T.μ.app (S.obj (S.obj (T.obj (S.obj X)))) ≫
      (T.map (S.μ.app (T.obj (S.obj X))) ≫ T.map (δ.app (S.obj X))) ≫
      T.μ.app (S.obj (S.obj X)) ≫ T.map (S.μ.app X) := by {
        simp only [endofunctorMonoidalCategory_tensorObj_obj, Category.assoc]}
    rw [this]
    rw [← map_comp]
    rw [← map_comp]
    have : T.map (S.map ((T.map (δ.app (S.obj X)) ≫
    T.μ.app (S.obj (S.obj X))) ≫ T.map (S.μ.app X))) ≫
    T.map (δ.app (S.obj X)) ≫ T.μ.app (S.obj (S.obj X)) ≫ T.map (S.μ.app X)=
      (T.map (S.map ((T.map (δ.app (S.obj X)) ≫
    T.μ.app (S.obj (S.obj X))) ≫ (T.map (S.μ.app X)))) ≫
    T.map (δ.app (S.obj X))) ≫
      T.μ.app (S.obj (S.obj X)) ≫ T.map (S.μ.app X) := sorry
    rw [this]
    rw [← map_comp]
    --have := distrib_naturality
    have := unit_left_components (S:=S) (T:=T) (X:=(S.obj X))
    have := unit_right_components (S:=S) (T:=T) (X:=(S.obj X))
    have := mul_left_components (S:=S) (T:=T) (X:=(S.obj X))
    have := mul_right_components (S:=S) (T:=T) (X:=(S.obj X))







  }
  left_unit X := by {
    sorry
    -- simp only [comp_obj, Functor.id_obj, unit_exchange, NatTrans.comp_app,
    --   endofunctorMonoidalCategory_whiskerRight_app, endofunctorMonoidalCategory_tensorObj_obj,
    --   endofunctorMonoidalCategory_whiskerLeft_app, endofunctorMonoidalCategory_tensorMap_app,
    --   ]
    -- have :  (T.η.app (T.obj (S.obj X)) ≫ T.map (S.η.app (T.obj (S.obj X)))) ≫
    -- T.map (δ.app (S.obj X)) ≫ T.μ.app (S.obj (S.obj X)) ≫ T.map (S.μ.app X) =
    --  (T.η.app (T.obj (S.obj X)) ≫ (T.map (S.η.app (T.obj (S.obj X)))) ≫
    -- T.map (δ.app (S.obj X))) ≫ T.μ.app (S.obj (S.obj X)) ≫ T.map (S.μ.app X)  := by {
    --   simp only [Functor.id_obj, endofunctorMonoidalCategory_tensorObj_obj, Category.assoc]
    -- }
    -- --rw [this]
    -- --rw [← map_comp]
    -- have:= Monad.left_unit (C:=C) T (X:=((S.obj X)))
    -- simp only [Functor.id_obj] at this
    -- simp only [Category.assoc]
    -- rw [← this]
    -- refine T.η.app (T.obj (S.obj X)) ≫= ?_










  }
  right_unit := sorry

theorem comp_unit {S T : Monad C} [DistribLaw S T] : (comp S T).η = T.η ≫ (S.η ▷ T.1) := by
  simp only [comp_η, unit_exchange]

theorem comp_toFunctor {S T : Monad C} [DistribLaw S T] :
    (comp S T).toFunctor = S.toFunctor ⋙ T.toFunctor := rfl

#check Mon_
#check Semiring

variable (C) [CartesianMonoidalCategory C] [ListArithmetic C] [WithBags C]

instance distribLawListBag: DistribLaw (list.monad C) (bag.monad C) where
  δ := {
    app X := list.lift <| bag.map list.singleton
    naturality := by {
      intros X Y f
      simp only [endofunctorMonoidalCategory_tensorObj_obj,
        endofunctorMonoidalCategory_tensorObj_map]
      sorry



    }
  }
  unit_left := sorry
  unit_right := sorry
  mul_left := sorry
  mul_right := sorry

def Semiring_ :=  LiftingMonad.monad (list.monad C) (bag.monad C) |>.Algebra

namespace Semiring_

variable (α : Semiring_ C)

def X : C := α.A.A

instance mon_Class : Mon_Class α.X where
  one := sorry
  mul := sorry
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry

def mon : Mon_ C where
  X := α.X

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

instance commMon : CommMon_ C where
  X := α.X
  mon := sorry
  comm := sorry

end Semiring_

end Monad

end CategoryTheory
