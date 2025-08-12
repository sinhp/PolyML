/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Algebra
import PolyML.ListArithmetic
import PolyML.FreeMon

/-
In this file, we define `bag A` as the free commutative monoid on `A`,
and establish useful relations between `bag A` and `list A`.

We also that show that any internal commutative monoid structure is the same as the data of an
algbera for the bag monad. Given a monoid structure on `A`, we define an aggregator morphism
`bag A ⟶ A` as the structure map of the algebra.

Therefore a bag structure on `A` is equivalent to the data of an aggregator.

-/

namespace CategoryTheory

open Category CategoryTheory Recursive ListArithmetic Functor MonoidalCategory
  Mon_Class CommMon_ Monad

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

def endofunctor : C ⥤ C :=
  WithBags.functor ⋙ CommMon_.forget C

instance monClass : Mon_Class (bag A) := bagMon A |> Mon_.mon

instance isCommMon : IsCommMon (bag A) := freeCommMon A |> CommMon_.comm

def nil : 𝟙_C ⟶ bag A := η

def append : bag A ⊗ bag A ⟶ bag A := μ

/-- `append` is symmetric because for bags. -/
@[reassoc (attr := simp)]
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
  dsimp [cons, snoc]
  nth_rw 2 [← append_symm]
  simp only [BraidedCategory.braiding_naturality_left_assoc]

/-- Given a commutative monoid object `M` in `C`, this lifts
  `f : A ⟶ M.X` to a morphism from `bag A` to `M.X`. -/
def lift {M : CommMon_ C} (f : A ⟶ M.X) : bag A ⟶ M.X :=
  bagMon.lift f |> (CommMon_.forget C).map

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
def map {B : C} (f : A ⟶ B) : bag A ⟶ bag B := bag.endofunctor.map f

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
  rw [map_eq_lift, lift_mul]

theorem cons_map {B : C} {f : A ⟶ B} :
    (f ⊗ₘ map f) ≫ cons = cons ≫ map f := by {
  dsimp [cons, append, bag]
  rw [Category.assoc, ← append_map]
  have := map_singleton (C:=C) (f:= (map f ⊗ₘ map f))
  rw [← Category.assoc, ← Category.assoc]
  refine ?_ =≫ μ
  ext
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
    CartesianMonoidalCategory.tensorHom_fst_assoc,
    CartesianMonoidalCategory.tensorHom_fst,
    CartesianMonoidalCategory.whiskerRight_fst_assoc, map_singleton]
  · simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
    CartesianMonoidalCategory.tensorHom_snd,
    CartesianMonoidalCategory.whiskerRight_snd_assoc]}

def ofList [ListArithmetic C] : list A ⟶ bag A :=
  list.lift (bag.singleton)

theorem ofList_nil [ListArithmetic C] :
    list.nil ≫ ofList = bag.nil (A:= A) := by
  simp only [bag.nil, ofList, singleton, list.nil, list.lift,list.foldl]
  simp only [plist.nil_rec]

theorem ofList_cons [ListArithmetic C] :
    list.cons ≫ ofList = A ◁ ofList ≫ bag.cons := by
  dsimp [ofList, list.lift, list.foldl, list.cons]
  rw [plist.cons_rec]
  refine A ◁ plist.rec η ((β_ A (bagMon A).X).hom ≫ (bagMon A).X ◁ singleton ≫ μ) ≫= ?_
  dsimp [cons, bag.append, bag]
  rw [← BraidedCategory.braiding_naturality_left_assoc]
  rw [IsCommMon.mul_comm, forget₂Mon_obj_mul]

/-
TODO: show that `ofList` is a quotient morphism. The relation should be thought of as
the permutation relation on lists, i.e. `l1 ~ l2` if `l1` can be obtained from `l2` by permuting the elements.

Tip: can we show for instance that this map is an effective epi? If so, every effective epi is regular and therefore W is `perm` relation.
-/

variable (C)

def monad : Monad C :=
  WithBags.adj |> Adjunction.toMonad

variable {C}

theorem monad_obj : (monad C).obj A = bag A := rfl

def join : bag (bag A) ⟶ bag A := (monad C).μ.app A

namespace algebra

/-- A commutative monoid structure on `A` gives rise to an algebra for the `bag` monad. -/
@[simps!]
def ofCommMon (M : CommMon_ C) : Algebra (monad C) where
  A := M.X
  a := lift (𝟙 _)
  unit := sorry
  assoc := sorry

instance monClassOfAlgebra {α : Algebra (monad C)} :
    Mon_Class ((monad C).obj α.A) := by
  dsimp [monad_obj]
  infer_instance

--#check append_map
/-- An algebra for the `bag` monad is a commutative monoid structure. -/
instance monClassOf (α : Algebra (monad C)) : Mon_Class (α.A) where
  one := η ≫ α.a
  mul := (singleton ⊗ₘ singleton) ≫ μ ≫ α.a
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry

instance isCommMon {α : Algebra (monad C)} : IsCommMon (α.A) where
  mul_comm := by {
  dsimp [Mon_Class.mul]
  rw [tensorHom_def', ← Category.assoc]
  rw [← BraidedCategory.braiding_naturality_left_assoc]
  rw [← BraidedCategory.braiding_naturality_right]
  rw [Category.assoc, Category.assoc]
  simp only [IsCommMon.mul_comm_assoc, forget₂Mon_obj_mul, Category.assoc]
  exact Eq.symm (whisker_exchange_assoc singleton singleton (μ ≫ α.a))}

def commMonOf (α : Algebra (monad C)) : CommMon_ C where
  X := α.A

end algebra

open algebra

def aggregator (M : CommMon_ C) : bag M.X ⟶ M.X :=
  (ofCommMon M).a

theorem aggregator_one {M : CommMon_ C} :
    η ≫ aggregator M = η := by
  dsimp [aggregator, ofCommMon, lift]
  simp only [IsMon_Hom.one_hom]

theorem aggregator_mul {M : CommMon_ C} :
    μ ≫ aggregator M = (aggregator M ⊗ₘ aggregator M) ≫ μ := by
  dsimp [aggregator, ofCommMon,lift]
  simp only [IsMon_Hom.mul_hom]

theorem aggregator_singleton {M : CommMon_ C} :
    singleton ≫ aggregator M = 𝟙 M.X := by
  dsimp [aggregator, ofCommMon]
  rw [lift_singleton]

theorem aggregator_join {M : CommMon_ C} :
    join ≫ aggregator M = (map <| aggregator M) ≫ aggregator M := by
  dsimp [join, aggregator, ofCommMon]
  have hassoc := (ofCommMon M).assoc
  dsimp [ofCommMon] at *
  rw [hassoc]
  rfl

theorem aggregator_map {M : CommMon_ C} {f : M.X ⟶ M'.X} :
    map f ≫ aggregator M' = aggregator M ≫ f := by
  sorry

theorem aggregator_ofList [ListArithmetic C] {M : CommMon_ C} :
    ofList ≫ bag.aggregator M = list.aggregator M.toMon_ := by
  sorry

end bag
end CategoryTheory
