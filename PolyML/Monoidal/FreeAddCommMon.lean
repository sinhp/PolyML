/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Algebra
import PolyML.Monoidal.ListArithmetic
import PolyML.Monoidal.FreeMon
import PolyML.ForMathlib.Monoidal.AddCommMon_

/-! # The Free Commutative Monoid Monad

In this file, we define `bag A` as the free commutative monoid on `A`,
and establish useful relations between `bag A` and `list A`.

We also that show that any internal commutative monoid structure is the same as the data of an
algbera for the bag monad. Given a monoid structure on `A`, we define an aggregator morphism
`bag A ⟶ A` as the structure map of the algebra.

Therefore a bag structure on `A` is equivalent to the data of an aggregator.
-/


namespace CategoryTheory

open Category CategoryTheory ListArithmetic Functor MonoidalCategory
  AddMon_Class AddCommMon_ Monad

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]


variable (C)

class WithBags where
  functor : C ⥤ AddCommMon_ C
  adj : functor ⊣ AddCommMon_.forget C

variable {C} [WithBags C]

/-- The common monoid structure on `bag A` is given by the free commutative monoid functor. -/
def freeAddCommMon (A : C) : AddCommMon_ C := WithBags.functor.obj A

def freeAddCommMon.lift {A : C} {M : AddCommMon_ C} (f : A ⟶ M.X) : freeAddCommMon A ⟶ M :=
  (WithBags.adj.homEquiv A M).invFun f

/-- The monoid structure on `bag A`. -/
def bagMon (A : C) : AddMon_ C := freeAddCommMon A |>.toAddMon_

def bagMon.lift {A : C} {M : AddCommMon_ C} (f : A ⟶ M.X) : bagMon A ⟶ M.toAddMon_ :=
  (freeAddCommMon.lift f) |> (AddCommMon_.forget₂Mon_ C).map

/-- The underlying type of the free commutative monoid on `A`. -/
abbrev bag (A : C) : C := bagMon A |>.X

namespace bag

variable {A : C}

def endofunctor : C ⥤ C :=
  WithBags.functor ⋙ AddCommMon_.forget C

instance addMonClass : AddMon_Class (bag A) := bagMon A |> AddMon_.mon

instance isCommMon : IsAddCommMon (bag A) := freeAddCommMon A |> AddCommMon_.comm

def nil : 𝟙_C ⟶ bag A := η

def append : bag A ⊗ bag A ⟶ bag A := μ

/-- `append` is symmetric because for bags. -/
@[reassoc (attr := simp)]
theorem braiding_append : (β_ (bag A) (bag A)).hom ≫ append = append := by
  dsimp [bag, append]
  simp only [IsAddCommMon.add_comm, forget₂Mon_obj_mul]

def singleton : A ⟶ bag A := WithBags.adj.unit.app A

def cons : A ⊗ bag A ⟶ bag A := (singleton ▷ bag A) ≫ append

def snoc : bag A ⊗ A ⟶ bag A := (bag A ◁ singleton) ≫ append

/-- Appending an element as head or tail is the same operation for bags. -/
theorem braiding_snoc_eq_cons : (β_ A (bag A)).hom ≫ snoc = cons := by
  dsimp [cons, snoc]
  nth_rw 2 [← braiding_append]
  simp only [BraidedCategory.braiding_naturality_left_assoc]

/-- Given a commutative monoid object `M` in `C`, this lifts
`f : A ⟶ M.X` to a morphism from `bag A` to `M.X`. -/
def lift {M : AddCommMon_ C} (f : A ⟶ M.X) : bag A ⟶ M.X :=
  bagMon.lift f |> (AddCommMon_.forget C).map

theorem lift_one {M : AddCommMon_ C} {f : A ⟶ M.X} :
    η ≫ lift f = η := by
  dsimp [lift]
  simp only [IsAddMon_Hom.zero_hom]

theorem lift_mul {M : AddCommMon_ C} {f : A ⟶ M.X} :
    μ ≫ lift f = (lift f ⊗ₘ lift f) ≫ μ := by
  dsimp [lift]
  simp only [IsAddMon_Hom.add_hom]

theorem lift_singleton {M : AddCommMon_ C} {f : A ⟶ M.X} :
  singleton ≫ lift f = f := by
  dsimp [singleton, lift, bagMon.lift, freeAddCommMon.lift]
  exact (WithBags.adj.homEquiv A M).right_inv f

/-- The functorial action of `bag` on morphisms. -/
def map {B : C} (f : A ⟶ B) : bag A ⟶ bag B := bag.endofunctor.map f

theorem map_eq_lift {B : C} (f : A ⟶ B) : map f = lift (f ≫ singleton) := by
  sorry

theorem map_lift_eq_lift_comp {M : AddCommMon_ C} {B : C} (f : A ⟶ B) (g : B ⟶ M.X) :
    map f ≫ lift g = lift (f ≫ g) := by
  dsimp [lift]
  have := Adjunction.homEquiv_naturality_left_symm (C:=C) (WithBags.adj) (Y:=M) (X:=B) (X':=A) f g
  dsimp [bagMon.lift, freeAddCommMon.lift, Adjunction.homEquiv, map, endofunctor]
  simp_all only [map_comp, comp', Category.assoc, AddMon_.comp_hom', toAddMon__X]

@[simp]
theorem map_nil {B : C} {f : A ⟶ B} :
    η ≫ map f = η := by
  rw [map_eq_lift]
  dsimp [lift]
  simp only [IsAddMon_Hom.zero_hom, forget₂Mon_obj_one]

@[simp]
theorem singleton_naturality {B : C} {f : A ⟶ B} :
    singleton ≫ map f = f ≫ singleton := by
  rw [map_eq_lift, lift_singleton]

theorem append_map {B : C} {f : A ⟶ B} : (map f ⊗ₘ map f) ≫ μ = μ ≫ map f := by
  rw [map_eq_lift, lift_mul]

theorem self_tensor_map_self_cons {B : C} {f : A ⟶ B} :
    (f ⊗ₘ map f) ≫ cons = cons ≫ map f := by
  dsimp [cons, append, bag]
  rw [Category.assoc, ← append_map]
  have := singleton_naturality (C:=C) (f:= (map f ⊗ₘ map f))
  rw [← Category.assoc, ← Category.assoc]
  refine ?_ =≫ μ
  sorry

/-- A trick/glue to make an additive monoid to a monoid so that we can define `ofList`. -/
instance toMon_ {X : C} [AddMon_Class X] : Mon_Class X where
  one := zero
  mul := add
  one_mul := AddMon_Class.zero_add X
  mul_one := AddMon_Class.add_zero X
  mul_assoc :=  AddMon_Class.add_assoc X

def list.lift' [ListArithmetic C] {X : C} {M : AddMon_ C} (f : X ⟶ M.X) : list X ⟶ M.X :=
  list.foldr ((f ▷ M.X) ≫ μ[M.X]) η[M.X]


def ofList [ListArithmetic C] : list A ⟶ bag A := list.lift' (bag.singleton)

theorem ofList_nil [ListArithmetic C] :
    list.nil ≫ ofList = bag.nil (A:= A) := by
  simp only [bag.nil, ofList, singleton, list.nil, list.lift,list.foldr]
  simp only [plist.nil_rec]

theorem ofList_cons [ListArithmetic C] :
    list.cons ≫ ofList = A ◁ ofList ≫ bag.cons := by
  dsimp [ofList, list.lift, list.foldr, list.cons]
  rw [plist.cons_rec]
  refine _ ≫= ?_
  dsimp [cons, bag.append, bag]

/-
TODO: show that `ofList` is a quotient morphism. The relation should be thought of as
the permutation relation on lists, i.e. `l1 ~ l2` if `l1` can be obtained from `l2` by permuting the elements.

Tip: can we show for instance that this map is an effective epi? If so, every effective epi is regular and therefore W is `perm` relation.
-/

variable (C)

def monad : Monad C := WithBags.adj |> Adjunction.toMonad

variable {C}

theorem monad_obj : (monad C).obj A = bag A := rfl

def join : bag (bag A) ⟶ bag A := (monad C).μ.app A

namespace algebra

/-- A commutative monoid structure on `A` gives rise to an algebra for the `bag` monad. -/
@[simps!]
def ofAddCommMon (M : AddCommMon_ C) : Algebra (monad C) where
  A := M.X
  a := lift (𝟙 _)
  unit := by {
    have := CategoryTheory.Adjunction.unit_comp_map_eq_iff (C:=C)
     (WithBags.adj) (A:=M.X) (B:=M) (f:= (bagMon.lift (𝟙 M.X)))
    dsimp [monad,lift]
    simp only [AddCommMon_.forget_obj, Functor.id_obj, comp_obj,
      AddCommMon_.forget_map, comp'] at this
    rw [this]
    exact rfl
  }
  assoc := sorry

instance monClassOfAlgebra {α : Algebra (monad C)} : Mon_Class ((monad C).obj α.A) := by
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
  mul_comm := by
    dsimp [Mon_Class.mul]
    rw [tensorHom_def', ← Category.assoc]
    rw [← BraidedCategory.braiding_naturality_left_assoc]
    rw [← BraidedCategory.braiding_naturality_right]
    rw [Category.assoc, Category.assoc]
    simp only [IsCommMon.mul_comm_assoc, forget₂Mon_obj_mul, Category.assoc]
    exact Eq.symm (whisker_exchange_assoc singleton singleton (μ ≫ α.a))

def commMonOf (α : Algebra (monad C)) : AddCommMon_ C where
  X := α.A

end algebra

open algebra

def aggregator (M : AddCommMon_ C) : bag M.X ⟶ M.X := (ofCommMon M).a

theorem aggregator_eq_lift {M : AddCommMon_ C} : aggregator M = lift (𝟙 M.X) := by
  dsimp [aggregator, ofCommMon, lift]

theorem aggregator_one {M : AddCommMon_ C} : η ≫ aggregator M = η := by
  dsimp [aggregator, ofCommMon, lift]
  simp only [IsMon_Hom.one_hom]

theorem aggregator_mul {M : AddCommMon_ C} :
    μ ≫ aggregator M = (aggregator M ⊗ₘ aggregator M) ≫ μ := by
  dsimp [aggregator, ofCommMon,lift]
  simp only [IsMon_Hom.mul_hom]

theorem aggregator_singleton {M : AddCommMon_ C} : singleton ≫ aggregator M = 𝟙 M.X := by
  dsimp [aggregator, ofCommMon]
  rw [lift_singleton]

theorem aggregator_join {M : AddCommMon_ C} :
    join ≫ aggregator M = (map <| aggregator M) ≫ aggregator M := by
  dsimp [join, aggregator, ofCommMon]
  have hassoc := (ofCommMon M).assoc
  dsimp [ofCommMon] at *
  rw [hassoc]
  rfl

theorem aggregator_map {M : AddCommMon_ C} {f : M.X ⟶ M'.X} :
    map f ≫ aggregator M' = aggregator M ≫ f := by
  sorry

theorem aggregator_ofList [ListArithmetic C] {M : AddCommMon_ C} :
    ofList ≫ bag.aggregator M = M.toMon_.aggregator := by
  sorry

end bag

end CategoryTheory
