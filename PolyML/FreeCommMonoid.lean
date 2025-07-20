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

open Category CategoryTheory Recursive ListArithmetic Functor MonoidalCategory Mon_Class

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
[Recursive C] [ListArithmetic C]

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

variable (C)

class WithBags where
  bagFunctor : C ⥤ CommMon_ C
  adj : bagFunctor ⊣ CommMon_.forget C

variable {C} [WithBags C]

def bag (A : C) : C :=
  WithBags.bagFunctor.obj A |>.X

namespace bag

def singleton {A : C} : A ⟶ bag A := WithBags.adj.unit.app A

def ofList {A : C} : list A ⟶ bag A :=
  sorry --list.lift (singleton)

/-
TODO: show that `ofList` is a quotient morphism. The relation should be thought of as
the permutation relation on lists, i.e. `l1 ~ l2` if `l1` can be obtained from `l2` by permuting the elements.
-/


end bag


end CategoryTheory
