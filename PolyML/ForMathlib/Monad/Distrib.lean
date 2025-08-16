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
import PolyML.BagInType
set_option maxHeartbeats 0
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
monads `S` and `T` is then defined as `⟨S ⋙ T, S.η ≫ T·η, TλS ≫ S.μ⟩`. A complete graphical proof
of unital and associativity laws for the composition monad is given on pages 34 and 35 of
[Marsden, Category Theory Using String Diagrams][https://arxiv.org/pdf/1401.7220]

The notion of distributive law was first introduced by Beck in 1969, and it is a central concept in the theory of monads. The paper is

Jon Beck, Distributive Laws, in: Seminar on Triples and Categorical Homology Theory, ETH 1966/67, Lecture Notes in Mathemativs, Springer (1969), Reprints in Theory and Applications of Categories 18 (2008) 1-303.
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
      rw [Monad.mu_naturality (T:=T) (f:=X.a), ← Category.assoc, ← Category.assoc]
      exact Category.assoc
        (δ.app (T.obj X.A) ≫ T.map (δ.app X.A)) (T.μ.app (S.obj X.A)) (T.map X.a)
    }⟩
    naturality α β f := by ext; apply Monad.mu_naturality}
  assoc α := by ext; apply Monad.assoc
  left_unit α := by ext; apply Monad.left_unit
  right_unit α := by ext; apply Monad.right_unit

variable {S T}

open CategoryTheory.Monad.Algebra

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
  unit := sorry
  assoc := sorry

@[reassoc (attr := simp)]
def distrib (α : (monad S T).Algebra) :
    δ.app (fstAlg α |>.A) ≫ T.map (fstAlg α).a ≫ (sndAlg α).a = S.map (sndAlg α).a ≫ (fstAlg α).a := by
  sorry

instance {T : Monad C} [DistribLaw S T] : Lift S T where
  toMonad := monad S T
  w := rfl
  respect_unit := by
    simp only [eqToHom_refl, comp_id]; ext α; rfl
  respect_mul := by
    simp only [eqToHom_refl, comp_id, id_comp]; ext α; rfl

end LiftingMonad

open DistribLaw

@[simp]
theorem unit_exchange {S T : Monad C} : S.η ≫ (S.1 ◁ T.η) = T.η ≫ (S.η ▷ T.1) := by
  ext X
  exact T.η.naturality <| S.η.app X

theorem CategoryTheory.Monad.comp.extracted_1 (S T : Monad C)
  [inst_1 : S.DistribLaw T] (X : C) :
  T.map (S.map (T.map (δ.app (S.obj X)) ≫
  T.μ.app (S.obj (S.obj X)) ≫ T.map (S.μ.app X))) ≫
  T.map (δ.app (S.obj X)) ≫ T.μ.app (S.obj (S.obj X)) ≫ T.map (S.μ.app X) =
  (T.map (δ.app (S.obj (T.obj (S.obj X)))) ≫
  T.μ.app (S.obj (S.obj (T.obj (S.obj X)))) ≫ T.map (S.μ.app (T.obj (S.obj X)))) ≫
  T.map (δ.app (S.obj X)) ≫ T.μ.app (S.obj (S.obj X)) ≫ T.map (S.μ.app X) := by
    let μₜ := T.μ.app
    let μₛ := S.μ.app
    let δ_ := NatTrans.app (δ (S:=S) (T:=T))
    let S_ := S.obj
    let T_ := T.obj
    change  T.map (S.map (T.map (δ_ (S_ X)) ≫ μₜ (S_ (S_ X)) ≫ T.map (μₛ X))) ≫
      T.map (δ_ (S_ X)) ≫ μₜ (S_ (S_ X)) ≫ T.map (μₛ X) =
       (T.map (δ_ (S_ (T_ (S_ X)))) ≫
      μₜ (S_ (S_ (T_ (S_ X)))) ≫ T.map (μₛ (T_ (S_ X)))) ≫
    T.map (δ_ (S_ X)) ≫ μₜ (S_ (S_ X)) ≫ T.map (μₛ X)
    have Tnat := T.mu_naturality
    have hr (X : C) := mul_right_components (X:=X) (S:=S) (T:=T)
    have hl (X : C) := (mul_left_components (X:=X) (S:=S) (T:=T)).symm
    nth_rw 1 [← T.μ.naturality, Functor.comp_map]
    simp only [map_comp]
    rw [Category.assoc]
    rw [← map_comp]
    rw [← map_comp]
    have := T.μ.naturality (f := S.μ.app (X))
    simp only [comp_obj, Functor.comp_map] at this
    nth_rw 1 [this]
    clear this
    have hd := distrib_naturality (S:=S) (T:=T) (f := ((S.μ.app X)))
    simp only [comp_obj, endofunctorMonoidalCategory_tensorObj_obj] at hd
    rw [map_comp]
    --nth_rw 1 [T.map_comp]
    nth_rw 2 [← Category.assoc]
    nth_rw 3 [← Category.assoc]
    nth_rw 1 [T.map_comp]
    have : ((T.map (S.map (T.μ.app (S.obj (S.obj X)))) ≫
    T.map (S.map (T.map (S.μ.app X)))) ≫ T.map (δ_ (S_ X))) =
     ((T.map (S.map (T.μ.app (S.obj (S.obj X)))) ≫
     (T.map (S.map (T.map (S.μ.app X)))) ≫ T.map (δ_ (S_ X)))) := sorry
    rw [this]
    clear this
    nth_rw 1 [← T.map_comp]
    rw [hd]
    rw [← T.map_comp]
    have : T.map (S.map (T.μ.app (S.obj (S.obj X))) ≫
     δ.app (S.obj (S.obj X)) ≫ T.map (S.map (S.μ.app X))) =
      T.map ((S.map (T.μ.app (S.obj (S.obj X))) ≫
      δ.app (S.obj (S.obj X))) ≫ T.map (S.map (S.μ.app X))) := sorry
    rw [this]
    clear this
    rw [hl]
    have hd' := distrib_naturality (S:=S) (T:=T)
       (f := (NatTrans.app (δ (S:=S) (T:=T)) (S.obj X)))
    simp only [endofunctorMonoidalCategory_tensorObj_obj] at hd'
    rw [T.map_comp]
    have : T.map (S.map (T.map (δ_ (S_ X)))) ≫
    (T.map (δ_ (T_ (S_ (S_ X))) ≫ T.map (δ_ (S_ (S_ X))) ≫
    μₜ (S_ (S_ (S_ X)))) ≫ T.map (T.map (S.map (μₛ X)))) ≫
      μₜ (S_ (S_ X)) ≫ T.map (μₛ X) =
      (T.map (S.map (T.map (δ_ (S_ X)))) ≫
    (T.map (δ_ (T_ (S_ (S_ X))) ≫ T.map (δ_ (S_ (S_ X))) ≫
    μₜ (S_ (S_ (S_ X)))) ≫ T.map (T.map (S.map (μₛ X))))) ≫
      μₜ (S_ (S_ X)) ≫ T.map (μₛ X) := by simp only [Category.assoc]
    rw [this,← T.map_comp,← T.map_comp]
    clear this
    have : (S.map (T.map (δ_ (S_ X))) ≫
        (δ_ (T_ (S_ (S_ X))) ≫ T.map (δ_ (S_ (S_ X))) ≫
        μₜ (S_ (S_ (S_ X)))) ≫ T.map (S.map (μₛ X)))
        =
         ((S.map (T.map (δ_ (S_ X))) ≫
        (δ_ (T_ (S_ (S_ X))))) ≫ (T.map (δ_ (S_ (S_ X))) ≫
        μₜ (S_ (S_ (S_ X)))) ≫ T.map (S.map (μₛ X))) := by {
          simp only [Category.assoc]
        }
    rw [this,hd']
    clear this
    rw [T.map_comp]
    rw [T.map_comp]
    have :
    ((T.map (δ.app (S.obj (T.obj (S.obj X)))) ≫
     T.map (T.map (S.map (δ.app (S.obj X))))) ≫
      T.map ((T.map (δ_ (S_ (S_ X))) ≫ μₜ (S_ (S_ (S_ X))))
      ≫ T.map (S.map (μₛ X)))) ≫
    μₜ (S_ (S_ X)) ≫ T.map (μₛ X) =
  ((T.map (δ_ (S_ (T_ (S_ X)))) ≫ μₜ (S_ (S_ (T_ (S_ X))))
   ≫ T.map (μₛ (T_ (S_ X)))) ≫ T.map (δ_ (S_ X))) ≫
    μₜ (S_ (S_ X)) ≫ T.map (μₛ X) ↔
    ((T.map (δ.app (S.obj (T.obj (S.obj X)))))) ≫
    (T.map (T.map (S.map (δ.app (S.obj X))))) ≫
      T.map ((T.map (δ_ (S_ (S_ X))) ≫ μₜ (S_ (S_ (S_ X))))
       ≫ T.map (S.map (μₛ X))) ≫
    μₜ (S_ (S_ X)) ≫ T.map (μₛ X) =
  (T.map (δ_ (S_ (T_ (S_ X))))) ≫ (μₜ (S_ (S_ (T_ (S_ X))))
   ≫ T.map (μₛ (T_ (S_ X))) ≫ T.map (δ_ (S_ X)) ≫
    μₜ (S_ (S_ X)) ≫ T.map (μₛ X)) := by {
      simp only [Category.assoc]
    }
    rw [this]
    clear this hd'


    dsimp [δ_,S_,T_]
    refine T.map (δ.app (S.obj (T.obj (S.obj X)))) ≫= ?_
    -- have HT := T.μ.naturality
    --   (f := (S.map (NatTrans.app (δ (S:=S) (T:=T)) (S.obj X))))
    -- simp only [endofunctorMonoidalCategory_tensorObj_obj,
    --   comp_obj, Functor.comp_map] at HT
    have :
    μₜ (S.obj (S.obj (T.obj (S.obj X)))) ≫
    T.map (μₛ (T.obj (S.obj X))) ≫ T.map (δ.app (S.obj X)) ≫
    μₜ (S.obj (S.obj X)) ≫ T.map (μₛ X)=
    (μₜ (S.obj (S.obj (T.obj (S.obj X)))) ≫
    T.map (μₛ (T.obj (S.obj X)))) ≫ T.map (δ.app (S.obj X)) ≫
     μₜ (S.obj (S.obj X)) ≫ T.map (μₛ X):= sorry
    rw [this]
    clear this
    -- nth_rw 1 [← T.μ.naturality]
    -- nth_rw 2 [← T.μ.naturality]
    -- simp only [Functor.comp_map]
    nth_rw 2 [← T.μ.naturality]
    simp only [Functor.comp_map]
    have :
      (T.map (T.map (μₛ (T.obj (S.obj X)))) ≫ T.μ.app (S.obj (T.obj (S.obj X)))) ≫
    T.map (δ.app (S.obj X)) ≫ μₜ (S.obj (S.obj X)) ≫ T.map (μₛ X)=
      (T.map (T.map (μₛ (T.obj (S.obj X)))) ≫ (T.μ.app (S.obj (T.obj (S.obj X)))) ≫
    T.map (δ.app (S.obj X))) ≫ μₜ (S.obj (S.obj X)) ≫ T.map (μₛ X):= by sorry
    rw [this]
    nth_rw 2 [← T.μ.naturality]
    simp only [Functor.comp_map]
    simp only [endofunctorMonoidalCategory_tensorObj_obj, Category.assoc, comp_obj]
    have :  T.map (T.map (μₛ (T.obj (S.obj X)))) ≫
    T.map (T.map (δ.app (S.obj X))) ≫
    T.μ.app (T.obj (S.obj (S.obj X))) ≫ μₜ (S.obj (S.obj X)) ≫ T.map (μₛ X) =
     (T.map (T.map (μₛ (T.obj (S.obj X)))) ≫
    T.map (T.map (δ.app (S.obj X)))) ≫
    (T.μ.app (T.obj (S.obj (S.obj X))) ≫ μₜ (S.obj (S.obj X)) ≫ T.map (μₛ X)) := sorry
    rw [this]
    clear this
    rw [← T.map_comp]
    rw [← T.map_comp]
    rw [← hr]
    nth_rw 2 [T.map_comp]
    nth_rw 2 [T.map_comp]
    have :
    (T.map (T.map (S.map (δ.app (S.obj X)))) ≫ T.map (T.map (δ.app (S.obj (S.obj X)) ≫
      T.map (S.μ.app (S.obj X))))) ≫
    T.μ.app (T.obj (S.obj (S.obj X))) ≫ μₜ (S.obj (S.obj X)) ≫ T.map (μₛ X) =
     T.map (T.map (S.map (δ.app (S.obj X)))) ≫ (T.map (T.map (δ.app (S.obj (S.obj X)) ≫
      T.map (S.μ.app (S.obj X)))) ≫
    T.μ.app (T.obj (S.obj (S.obj X))) ≫ μₜ (S.obj (S.obj X)) ≫ T.map (μₛ X)) := sorry
    rw [this]
    clear this
    refine  T.map (T.map (S.map (δ.app (S.obj X)))) ≫= ?_
    nth_rw 1 [T.map_comp]
    nth_rw 2 [T.map_comp]
    nth_rw 2 [T.map_comp]
    have :  (T.map (T.map (δ.app (S.obj (S.obj X)))) ≫
     T.map (μₜ (S.obj (S.obj (S.obj X))) ≫ T.map (S.map (μₛ X)))) ≫
    μₜ (S.obj (S.obj X)) ≫ T.map (μₛ X)
    =
     ((T.map (T.map (δ.app (S.obj (S.obj X))))) ≫
     (T.map (μₜ (S.obj (S.obj (S.obj X))) ≫ T.map (S.map (μₛ X)))) ≫
    μₜ (S.obj (S.obj X)) ≫ T.map (μₛ X)):= sorry
    rw [this]
    clear this
    have : (T.map (T.map (δ.app (S.obj (S.obj X)))) ≫ T.map (T.map (T.map (S.μ.app (S.obj X))))) ≫
    T.μ.app (T.obj (S.obj (S.obj X))) ≫ μₜ (S.obj (S.obj X)) ≫ T.map (μₛ X)
    =
     ((T.map (T.map (δ.app (S.obj (S.obj X))))) ≫ (T.map (T.map (T.map (S.μ.app (S.obj X))))) ≫
    T.μ.app (T.obj (S.obj (S.obj X))) ≫ μₜ (S.obj (S.obj X)) ≫ T.map (μₛ X)) := sorry
    rw [this]
    clear this
    refine  (T.map (T.map (δ.app (S.obj (S.obj X))))) ≫= ?_
    -- nth_rw 1 [← T.μ.naturality]
    -- simp only [endofunctorMonoidalCategory_tensorObj_obj, comp_obj, Functor.comp_map, map_comp]
    -- clear this
    -- nth_rw 1 [← T.μ.naturality]
    -- simp only [endofunctorMonoidalCategory_tensorObj_obj, comp_obj, Functor.comp_map]
    -- nth_rw 1 [← T.μ.naturality]
    -- simp only [endofunctorMonoidalCategory_tensorObj_obj, comp_obj, Functor.comp_map]
    -- have :  T.μ.app (T.obj (S.obj (S.obj X))) ≫ T.map (T.map (μₛ X)) ≫ T.μ.app (S.obj X)=
    --  (T.μ.app (T.obj (S.obj (S.obj X))) ≫ T.map (T.map (μₛ X))) ≫ T.μ.app (S.obj X) := sorry
    -- rw [this]
    -- clear this
    -- nth_rw 1 [← T.μ.naturality]
    -- simp only [comp_obj, Functor.comp_map]
    -- have := T.μ.naturality (f:= (μₛ X))
    -- simp only [comp_obj, Functor.comp_map] at this
    -- rw [this]
    -- clear this




















#exit


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
      endofunctorMonoidalCategory_tensorMap_app, Functor.comp_map]
    have hr := mul_right_components (X := ((S.obj X))) (S := S) (T:=T)
    rw [Category.assoc, Category.assoc]
    nth_rw 6 [← Category.assoc]
    rw [← map_comp, ← hr]
    clear * - hr
    nth_rw 1 [T.map_comp]
    simp only [Functor.map_comp, Category.assoc] at *
    nth_rw 1 [← T.μ.naturality]
    simp only [comp_obj, Functor.comp_map,
      endofunctorMonoidalCategory_tensorObj_obj]
    nth_rw 3 [← Category.assoc]
    rw [← Category.assoc, ← map_comp, ← map_comp]
    rw [← Category.assoc, ← map_comp, ← Category.assoc, ← map_comp]
    have hd := distrib_naturality (S:=S) (T:=T) (f := ((S.μ.app X)))
    simp only [comp_obj, endofunctorMonoidalCategory_tensorObj_obj] at hd
    rw [hd]
    clear * - hd
    nth_rw 2 [map_comp]
    have :
    (((S.map (T.map (δ.app (S.obj X))) ≫ S.map (T.μ.app (S.obj (S.obj X)))) ≫
      δ.app (S.obj (S.obj X)) ≫ T.map (S.map (S.μ.app X)))) =
    (((S.map (T.map (δ.app (S.obj X))) ≫
    (S.map (T.μ.app (S.obj (S.obj X)))) ≫ δ.app (S.obj (S.obj X))) ≫
      T.map (S.map (S.μ.app X)))) := by {
      simp only [Category.assoc]}
    rw [this]
    have hl := mul_left_components (X := (S.obj (S.obj X))) (S := S) (T:=T)
    simp only [endofunctorMonoidalCategory_tensorObj_obj, comp_obj] at hl
    rw [← hl]
    clear * - hl
    rw [T.map_comp]
    rw [← Category.assoc]
    have hd' := distrib_naturality (S:=S) (T:=T)
       (f := (NatTrans.app (δ (S:=S) (T:=T)) (S.obj X)))
    simp only [endofunctorMonoidalCategory_tensorObj_obj] at hd'
    rw [hd']
    simp only [endofunctorMonoidalCategory_tensorObj_obj,
      Category.assoc, map_comp]
    clear * -hd'
    refine T.map (δ.app (S.obj (T.obj (S.obj X)))) ≫= ?_
    nth_rw 2 [← Category.assoc]
    have := T.μ.naturality
      (f := (S.map (NatTrans.app (δ (S:=S) (T:=T)) (S.obj X))))
    simp only [endofunctorMonoidalCategory_tensorObj_obj,
      comp_obj, Functor.comp_map] at this
    nth_rw 4 [← Category.assoc]
    rw [← this]
    nth_rw 2 [Category.assoc]
    refine T.map (T.map (S.map (δ.app (S.obj X)))) ≫= ?_
    clear * -this
    have := T.μ.naturality
      (f := ((NatTrans.app (δ (S:=S) (T:=T)) (S.obj (S.obj X)))))
    simp only [endofunctorMonoidalCategory_tensorObj_obj,
      comp_obj, Functor.comp_map] at this
    nth_rw 3 [← Category.assoc]
    rw [← this]
    simp only [Category.assoc]
    refine T.map (T.map (δ.app (S.obj (S.obj X)))) ≫= ?_
    clear * -this

    have := T.μ.naturality (f := (T.map (S.μ.app (S.obj X))))
    simp only [comp_obj, Functor.comp_map] at this
    nth_rw 3 [← Category.assoc]
    simp only [endofunctorMonoidalCategory_tensorObj_obj, Category.assoc]
    clear * -this
    have := T.μ.naturality (f := (S.map (S.μ.app X)))
    simp only [comp_obj, Functor.comp_map] at this
    rw [← Category.assoc,← map_comp]
    rw [← this]
    clear this
    have h6 := T.μ.naturality (T.map (S.μ.app (S.obj X)))
    simp only [comp_obj, Functor.comp_map] at h6
    nth_rw 2 [← Category.assoc]
    rw [← h6]
    clear h6 this
    have h7 := T.μ.naturality (T.map ((S.μ.app X)))
    simp only [comp_obj, Functor.comp_map] at h7
    have : (T.map (T.map (T.map (S.μ.app (S.obj X)))) ≫
      T.μ.app (T.obj (S.obj (S.obj X)))) ≫
    T.map (T.map (S.μ.app X)) ≫ T.μ.app (S.obj X)=
    (T.map (T.map (T.map (S.μ.app (S.obj X)))) ≫
      (T.μ.app (T.obj (S.obj (S.obj X)))) ≫
    T.map (T.map (S.μ.app X))) ≫ T.μ.app (S.obj X):= by {sorry}
    --rw [← h7]

    --clear * -h7 this
    have hr := mul_right_components (X := ((S.obj X))) (S := S) (T:=T)

    sorry
  }

  left_unit X := by {
    simp only [comp_obj, Functor.id_obj, unit_exchange, NatTrans.comp_app,
      endofunctorMonoidalCategory_whiskerRight_app,
      endofunctorMonoidalCategory_tensorObj_obj,
      endofunctorMonoidalCategory_whiskerLeft_app,
      endofunctorMonoidalCategory_tensorMap_app]
    have hdistrib_unit_right :=
      DistribLaw.unit_right_components (X:=(S.obj X)) (S:= S) (T:=T)
    have hleftunit := T.left_unit (X := (S.obj X))
    simp only [Functor.id_obj] at hleftunit
    nth_rw 1 [Category.assoc]
    nth_rw 2 [← Category.assoc]
    rw [← map_comp, hdistrib_unit_right]
    simp only [Functor.id_obj]
    rw [← hleftunit, ← Category.assoc, ← T.unit_naturality, ← Category.assoc]
    simp only [Category.assoc, left_unit, Functor.id_obj, comp_id,
       ← map_comp, map_id, hleftunit]
  }

  right_unit X := by {
    simp only [comp_obj, Functor.id_obj, NatTrans.comp_app,
      endofunctorMonoidalCategory_whiskerRight_app,
      endofunctorMonoidalCategory_tensorObj_obj,
      endofunctorMonoidalCategory_whiskerLeft_app,
      endofunctorMonoidalCategory_tensorMap_app]
    simp only [Functor.comp_map, map_comp]
    have hdistrib_unit_left :=
      DistribLaw.unit_left_components (X:=(S.obj X)) (S:= S) (T:=T)
    have h_monad_unit := T.right_unit ((S.obj (S.obj X)))
    rw [← T.map_comp, ← Category.assoc, ← T.map_comp]
    rw [Category.assoc, hdistrib_unit_left, T.map_comp]
    rw [Category.assoc]
    simp only [right_unit_assoc]
    rw [← map_comp]
    simp only [right_unit, Functor.id_obj, map_id]
  }

#exit
theorem comp_unit {S T : Monad C} [DistribLaw S T] :
    (comp S T).η = T.η ≫ (S.η ▷ T.1) := by
  simp only [comp_η, unit_exchange]

theorem comp_toFunctor {S T : Monad C} [DistribLaw S T] :
    (comp S T).toFunctor = S.toFunctor ⋙ T.toFunctor := rfl

-- #check Mon_
-- #check Semiring

variable (C) [CartesianMonoidalCategory C] [ListArithmetic C] [WithBags C]

instance distribLawListBag : DistribLaw (list.monad C) (bag.monad C) where
  δ := {
    app X := list.lift <| bag.map list.singleton
    naturality X Y f := by {
      sorry
    }
  }
  unit_left := sorry
  unit_right := sorry
  mul_left := sorry
  mul_right := sorry

def Semiring_ := LiftingMonad.monad (list.monad C) (bag.monad C) |>.Algebra

namespace Semiring_

variable (α : Semiring_ C)

def X : C := α.A.A

instance mon_Class : Mon_Class α.X where
  one := by {
    dsimp [X]
    sorry
  }
  mul := by {
    dsimp [X]
    sorry
  }
  one_mul := by
    sorry
  mul_one := by
    sorry
  mul_assoc := by
    sorry

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
