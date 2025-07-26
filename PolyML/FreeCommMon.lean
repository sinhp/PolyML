/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monoidal.CommMon_
import PolyML.FreeMon
import PolyML.ListArithmetic

/-
In this file, we define `bag A` as the free commutative monoid on `A`,
and establish useful relations between `bag A` and `list A`.
-/

namespace CategoryTheory

open Category CategoryTheory Recursive ListArithmetic Functor MonoidalCategory Mon_Class CommMon_

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

variable (C)

class WithBags where
  functor : C ⥤ CommMon_ C
  adj : functor ⊣ CommMon_.forget C

variable {C} [WithBags C]

/-- The common monoid structure on `bag A` is given by the free commutative monoid functor. -/
def freeCommMon (A : C) : CommMon_ C := WithBags.functor.obj A

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

def functor : C ⥤ C :=
  WithBags.functor ⋙ CommMon_.forget C

instance mon_Class : Mon_Class (bag A) := bagMon A |> Mon_.mon

instance isCommMon : IsCommMon (bag A) := freeCommMon A |> CommMon_.comm

def nil : 𝟙_C ⟶ bag A := η

def append : bag A ⊗ bag A ⟶ bag A := μ

/-- `append` is symmetric because for bags. -/
theorem append_symm : (β_ (bag A) (bag A)).hom ≫ append = append := by
  dsimp [bag, append]
  simp only [IsCommMon.mul_comm, forget₂Mon_obj_mul]

def singleton : A ⟶ bag A := WithBags.adj.unit.app A

def cons : A ⊗ bag A ⟶ bag A :=
  (singleton ▷ bag A) ≫ append

def snoc : bag A ⊗ A ⟶ bag A :=
  (bag A ◁ singleton) ≫ append

/-- Appending an element as head or tail is the same operation for bags. -/
theorem cons_snoc : (β_ A (bag A)).hom ≫ snoc = cons := by
  sorry

/-- Given a commutative monoid object `M` in `C`, this lifts
  `f : A ⟶ M.X` to a morphism from `bag A` to `M.X`. -/
def lift {M : CommMon_ C} (f : A ⟶ M.X) : bag A ⟶ M.X :=
  bagMon.lift f |> (forget C).map

theorem lift_one {M : CommMon_ C} {f : A ⟶ M.X} :
    η ≫ lift f = η := by
  dsimp [lift]
  simp only [IsMon_Hom.one_hom]

theorem lift_mul {M : CommMon_ C} {f : A ⟶ M.X} :
    μ ≫ lift f = (lift f ⊗ₘ lift f) ≫ μ := by
  dsimp [lift]
  simp only [IsMon_Hom.mul_hom]

theorem lift_singleton {M : CommMon_ C} {f : A ⟶ M.X} :
    singleton ≫ lift f = f := by
  sorry

/-- The functorial action of `bag` on morphisms. -/
def map {B : C} (f : A ⟶ B) : bag A ⟶ bag B := bag.functor.map f

theorem map_eq_lift  (f : A ⟶ B) : map f = lift (f ≫ singleton) := by
  sorry

@[simp]
theorem map_nil {B : C} {f : A ⟶ B} :
    η ≫ map f = η := by
  rw [map_eq_lift]
  dsimp [lift]
  simp only [IsMon_Hom.one_hom, forget₂Mon_obj_one]

@[simp]
theorem map_singleton {B : C} {f : A ⟶ B} :
    singleton ≫ map f = f ≫ singleton := by
  rw [map_eq_lift, lift_singleton]

theorem append_map {B : C} {f : A ⟶ B} :
    (map f ⊗ₘ map f) ≫ μ = μ ≫ map f := by
  rw [map_eq_lift]
  rw [lift_mul]

theorem cons_map {B : C} {f : A ⟶ B} :
    (f ⊗ₘ map f) ≫ cons = cons ≫ map f := by
  sorry
  -- dsimp [cons]
  -- dsimp [append]
  -- simp only [assoc, ← append_map, forget₂Mon_obj_mul]
  -- rw [map_eq_lift]
  -- simp only [← lift_mul]
  -- rw [← assoc]

def ofList [ListArithmetic C] : list A ⟶ bag A :=
  list.lift (bag.singleton)

theorem ofList_nil [ListArithmetic C] : list.nil ≫ ofList = bag.nil (A:= A) := by
  simp only [bag.nil, ofList, singleton, list.nil, list.lift,list.foldl]
  simp only [plist.rec_nil]

theorem ofList_cons [ListArithmetic C] :
    list.cons (A:= A) ≫ ofList = A ◁ ofList ≫ bag.cons := by
  simp only [ofList, singleton,list.lift,list.foldl]
  dsimp [list.cons]
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
