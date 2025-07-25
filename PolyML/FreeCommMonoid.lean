/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monoidal.CommMon_
import PolyML.FreeMonoid
import PolyML.ListArithmetic

/-
In this file, we define `bag A` as the free commutative monoid on `A`, and establish useful relations between `bag A` and `list A`.
-/


namespace CategoryTheory

open Category CategoryTheory Recursive ListArithmetic Functor MonoidalCategory Mon_Class CommMon_

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
[Recursive C] [ListArithmetic C]

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

variable (C)

class WithBags where
  bagFunctor : C ⥤ CommMon_ C
  adj : bagFunctor ⊣ CommMon_.forget C

variable {C} [WithBags C]

/-- The common monoid structure on `bag A` is given by the free commutative monoid functor. -/
def freeCommMon (A : C) : CommMon_ C := WithBags.bagFunctor.obj A

def freeCommMon.lift {M : CommMon_ C} (f : A ⟶ M.X) : freeCommMon A ⟶ M :=
  (WithBags.adj.homEquiv A M).invFun f

/-- The monoid structure on `bag A`. -/
def bagMon (A : C) : Mon_ C := freeCommMon A |>.toMon_

def bagMon.lift {A : C} {M : CommMon_ C} (f : A ⟶ M.X) : bagMon A ⟶ M.toMon_ :=
  (freeCommMon.lift f) |> (CommMon_.forget₂Mon_ C).map

/-- The underlying type of the free commutative monoid on `A`. -/
abbrev bag (A : C) : C := bagMon A |>.X

namespace bag

variable {A : C}

instance mon_Class : Mon_Class (bag A) := bagMon A |> Mon_.mon

instance isCommMon : IsCommMon (bag A) := freeCommMon A |> CommMon_.comm

def nil : 𝟙_C ⟶ bag A :=
  bagMon A |>.mon |>.one

def singleton : A ⟶ bag A := WithBags.adj.unit.app A

/-- Given a commutative monoid object `M` in `C`, this lifts `f : A ⟶ M.X` to a morphism from `bag A` to `M.X`. -/
def lift {M : CommMon_ C} (f : A ⟶ M.X) : bag A ⟶ M.X :=
  bagMon.lift f |> (forget C).map

#check η

theorem lift_one {M : CommMon_ C} {f : A ⟶ M.X} :
    η ≫ lift f = η := by
  sorry

theorem lift_mul {M : CommMon_ C} {f : A ⟶ M.X} :
    μ ≫ lift f = (lift f ⊗ₘ lift f) ≫ μ := by
  sorry

theorem lift_singleton {M : CommMon_ C} {f : A ⟶ M.X} :
    singleton ≫ lift f = f := by
  sorry

/-- The functorial action of `bag` on morphisms. -/
def map {B : C} (f : A ⟶ B) : bag A ⟶ bag B :=
  lift (f ≫ singleton)

theorem map_nil {M : CommMon_ C} {f : A ⟶ M.X} :
    η ≫ lift f = η := by
  sorry

def ofList : list A ⟶ bag A :=
  list.lift (bag.singleton)

theorem ofList_nil : list.nil ≫ ofList = bag.nil (A:= A) := by
  sorry


/-
TODO: show that `ofList` is a quotient morphism. The relation should be thought of as
the permutation relation on lists, i.e. `l1 ~ l2` if `l1` can be obtained from `l2` by permuting the elements.

Tip: can we show for instance that this map is an effective epi? If so, every effective epi is regular and therefore W is `perm` relation.
-/







/-
TODO:
*aggregator*
show that any internal commutative monoid structure is equivalent to the data of an aggregator.

Therefore a bag structure on `A` is equivalent to the data of an aggregator.

-/


end bag


end CategoryTheory
