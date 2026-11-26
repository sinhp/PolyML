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
  AddMonObj AddCommMon Monad

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]


variable (C)

class WithBags where
  functor : C ⥤ AddCommMon C
  adj : functor ⊣ AddCommMon.forget C

variable {C} [WithBags C]

/-- The common monoid structure on `bag A` is given by the free commutative monoid functor. -/
def freeAddCommMon (A : C) : AddCommMon C := WithBags.functor.obj A

def freeAddCommMon.lift {A : C} {M : AddCommMon C} (f : A ⟶ M.X) : freeAddCommMon A ⟶ M :=
  (WithBags.adj.homEquiv A M).invFun f

/-- The monoid structure on `bag A`. -/
def bagMon (A : C) : AddMon C := freeAddCommMon A |>.toAddMon

def bagMon.lift {A : C} {M : AddCommMon C} (f : A ⟶ M.X) : bagMon A ⟶ M.toAddMon :=
  (freeAddCommMon.lift f) |> (AddCommMon.forget₂Mon_ C).map

/-- The underlying type of the free commutative monoid on `A`. -/
abbrev bag (A : C) : C := bagMon A |>.X

namespace bag

variable {A : C}

def endofunctor : C ⥤ C :=
  WithBags.functor ⋙ AddCommMon.forget C

instance addMonClass : AddMonObj (bag A) := bagMon A |>.addMon

instance isCommMon : IsAddCommMonObj (bag A) := freeAddCommMon A |>.comm

def nil : 𝟙_C ⟶ bag A := η

def append : bag A ⊗ bag A ⟶ bag A := μ

/-- `append` is symmetric because for bags. -/
@[reassoc (attr := simp)]
theorem braiding_append : (β_ (bag A) (bag A)).hom ≫ append = append := by
  dsimp [bag, append]
  simp only [IsAddCommMonObj.add_comm, forget₂Mon_obj_mul]

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
def lift {M : AddCommMon C} (f : A ⟶ M.X) : bag A ⟶ M.X :=
  bagMon.lift f |> (AddCommMon.forget C).map

theorem lift_one {M : AddCommMon C} {f : A ⟶ M.X} :
    η ≫ lift f = η := by
  dsimp [lift]
  simp only [IsAddMonHom.zero_hom]

theorem lift_mul {M : AddCommMon C} {f : A ⟶ M.X} :
    μ ≫ lift f = (lift f ⊗ₘ lift f) ≫ μ := by
  dsimp [lift]
  simp only [IsAddMonHom.add_hom]

theorem lift_singleton {M : AddCommMon C} {f : A ⟶ M.X} :
  singleton ≫ lift f = f := by
  dsimp [singleton, lift, bagMon.lift, freeAddCommMon.lift]
  exact (WithBags.adj.homEquiv A M).right_inv f

/-- The functorial action of `bag` on morphisms. -/
def map {B : C} (f : A ⟶ B) : bag A ⟶ bag B := bag.endofunctor.map f

theorem map_eq_lift {B : C} (f : A ⟶ B) : map f = lift (f ≫ singleton) := by
  show (WithBags.functor.map f |> (AddCommMon.forget C).map) =
    (freeAddCommMon.lift (f ≫ singleton) |> (AddCommMon.forget C).map)
  congr 1
  show WithBags.functor.map f = freeAddCommMon.lift (f ≫ singleton)
  show WithBags.functor.map f = (WithBags.adj.homEquiv A (freeAddCommMon B)).invFun (f ≫ singleton)
  rw [show (WithBags.adj.homEquiv A (freeAddCommMon B)).invFun
      = (WithBags.adj.homEquiv A (freeAddCommMon B)).symm from rfl]
  apply (WithBags.adj.homEquiv A (freeAddCommMon B)).eq_symm_apply.mpr
  exact (WithBags.adj.unit.naturality f).symm

theorem map_lift_eq_lift_comp {M : AddCommMon C} {B : C} (f : A ⟶ B) (g : B ⟶ M.X) :
    map f ≫ lift g = lift (f ≫ g) := by
  dsimp [lift]
  have := Adjunction.homEquiv_naturality_left_symm (C:=C) (WithBags.adj) (Y:=M) (X:=B) (X':=A) f g
  dsimp [bagMon.lift, freeAddCommMon.lift, Adjunction.homEquiv, map, endofunctor]
  simp_all only [map_comp, comp', Category.assoc, AddMon.comp_hom', toAddMon_X]

@[simp]
theorem map_nil {B : C} {f : A ⟶ B} :
    η ≫ map f = η := by
  rw [map_eq_lift]
  dsimp [lift]
  simp only [IsAddMonHom.zero_hom, forget₂Mon_obj_one]

@[simp]
theorem singleton_naturality {B : C} {f : A ⟶ B} :
    singleton ≫ map f = f ≫ singleton := by
  rw [map_eq_lift, lift_singleton]

theorem append_map {B : C} {f : A ⟶ B} : (map f ⊗ₘ map f) ≫ μ = μ ≫ map f := by
  rw [map_eq_lift, lift_mul]

theorem self_tensor_map_self_cons {B : C} {f : A ⟶ B} :
    (f ⊗ₘ map f) ≫ cons = cons ≫ map f := by
  dsimp [cons, append]
  rw [Category.assoc, ← append_map, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [tensorHom_def, Category.assoc, whisker_exchange, ← Category.assoc,
    ← comp_whiskerRight, ← singleton_naturality, comp_whiskerRight, Category.assoc,
    ← tensorHom_def]

/-- A `def` (rather than `instance` to avoid clashing with native `MonObj` instances)
witnessing that any `AddMonObj` underlies a `MonObj`. Enable locally via
`attribute [local instance] toMon_` when needed. -/
def toMon_ {X : C} [AddMonObj X] : MonObj X where
  one := AddMonObj.zero
  mul := AddMonObj.add
  one_mul := AddMonObj.zero_add X
  mul_one := AddMonObj.add_zero X
  mul_assoc := AddMonObj.add_assoc X

def list.lift' [ListArithmetic C] {X : C} {M : AddMon C} (f : X ⟶ M.X) : list X ⟶ M.X :=
  list.foldr ((f ▷ M.X) ≫ μ[M.X]) η[M.X]

def ofList [ListArithmetic C] : list A ⟶ bag A := list.lift' (bag.singleton)

theorem ofList_nil [ListArithmetic C] :
    list.nil ≫ ofList = bag.nil (A:= A) := by
  simp only [bag.nil, ofList, list.lift', singleton, list.nil, list.foldr]
  simp only [plist.nil_rc]

theorem ofList_cons [ListArithmetic C] :
    list.cons ≫ ofList = A ◁ ofList ≫ bag.cons := by
  dsimp [ofList, list.lift', list.foldr, list.cons]
  rw [plist.cons_rc]
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

/-- Equip an additive commutative monoid object with the algebra structure obtained from
Monad.comparison. -/
def addCommMonToBagAlgebraFunctor : AddCommMon C ⥤ (monad C).Algebra :=
  Monad.comparison WithBags.adj

/-- A commutative monoid structure on `A` gives rise to an algebra for the `bag` monad. -/
def ofAddCommMon (M : AddCommMon C) : Algebra (monad C) :=
  addCommMonToBagAlgebraFunctor.obj M

@[simp]
theorem ofAddCommMon_A {M : AddCommMon C} : (ofAddCommMon M).A = M.X := rfl

@[simp]
theorem ofAddCommMon_a {M : AddCommMon C} : (ofAddCommMon M).a = lift (𝟙 M.X) := by
  have := CategoryTheory.Adjunction.unit_comp_map_eq_iff (C := C)
    (WithBags.adj) (A := M.X) (B := M) (f := (bagMon.lift (𝟙 M.X))) (𝟙 M.X)
  dsimp [monad, lift]
  simp only [Functor.map_id, Category.id_comp] at this
  symm
  congr
  apply this.mp
  simpa using lift_singleton

instance addMonObjOfAlgebra {α : Algebra (monad C)} : AddMonObj ((monad C).obj α.A) := by
  dsimp [monad_obj]; infer_instance

/-- An algebra for the `bag` monad is an additive monoid structure. -/
instance addMonObjOf (α : Algebra (monad C)) : AddMonObj (α.A) where
  zero := η ≫ α.a
  add := (singleton ⊗ₘ singleton) ≫ μ ≫ α.a
  zero_add := sorry
  add_zero := sorry
  add_assoc := sorry

instance isAddCommMonObjOf {α : Algebra (monad C)} : IsAddCommMonObj (α.A) where
  add_comm := by
    dsimp [AddMonObj.add]
    rw [tensorHom_def', ← Category.assoc, ← BraidedCategory.braiding_naturality_left_assoc,
        ← BraidedCategory.braiding_naturality_right, Category.assoc, Category.assoc]
    simp only [IsAddCommMonObj.add_comm_assoc, forget₂Mon_obj_mul, Category.assoc]
    exact (whisker_exchange_assoc singleton singleton (μ ≫ α.a)).symm

def commMonOf (α : Algebra (monad C)) : AddCommMon C where
  X := α.A

end algebra

open algebra

def aggregator (M : AddCommMon C) : bag M.X ⟶ M.X := (ofAddCommMon M).a

theorem aggregator_eq_lift {M : AddCommMon C} : aggregator M = lift (𝟙 M.X) :=
  ofAddCommMon_a

theorem aggregator_one {M : AddCommMon C} : η ≫ aggregator M = η := by
  rw [aggregator_eq_lift, lift_one]

theorem aggregator_mul {M : AddCommMon C} :
    μ ≫ aggregator M = (aggregator M ⊗ₘ aggregator M) ≫ μ := by
  rw [aggregator_eq_lift, lift_mul]

theorem aggregator_singleton {M : AddCommMon C} : singleton ≫ aggregator M = 𝟙 M.X := by
  rw [aggregator_eq_lift, lift_singleton]

theorem aggregator_join {M : AddCommMon C} :
    join ≫ aggregator M = (map <| aggregator M) ≫ aggregator M := by
  simpa [join, aggregator, ofAddCommMon] using (ofAddCommMon M).assoc

theorem aggregator_eq_counit_app {M : AddCommMon C} :
    aggregator M = (WithBags.adj.counit.app M).hom := by
  rw [aggregator_eq_lift]
  dsimp [lift, bagMon.lift, freeAddCommMon.lift]
  show ((WithBags.adj.homEquiv M.X M).invFun (𝟙 M.X) |>
    (AddCommMon.forget₂Mon_ C).map |> (AddCommMon.forget C).map) =
      (WithBags.adj.counit.app M).hom
  rw [show (WithBags.adj.homEquiv M.X M).invFun = (WithBags.adj.homEquiv M.X M).symm from rfl]
  rw [Adjunction.homEquiv_counit]
  show ((AddCommMon.forget C).map ((AddCommMon.forget₂Mon_ C).map
    (WithBags.functor.map (𝟙 M.X) ≫ WithBags.adj.counit.app M))) =
      (WithBags.adj.counit.app M).hom
  rw [Functor.map_id, Category.id_comp]
  rfl

/-- Aggregator is natural with respect to additive commutative monoid homomorphisms. -/
theorem aggregator_map' {M M' : AddCommMon C} {f : M ⟶ M'} :
    map f.hom ≫ aggregator M' = aggregator M ≫ f.hom := by
  have := (WithBags.adj.counit.naturality (X := M) (Y := M') f)
  have h_nat_hom := congr_arg (fun g => g.hom) this
  simp only [Functor.comp_map, Functor.id_map] at h_nat_hom
  rw [aggregator_eq_counit_app, aggregator_eq_counit_app]
  exact h_nat_hom

theorem aggregator_map {M M' : AddCommMon C} {f : M.X ⟶ M'.X} [IsAddMonHom f] :
    map f ≫ aggregator M' = aggregator M ≫ f :=
  aggregator_map' (M := M) (M' := M') (f := ⟨f⟩)

theorem aggregator_ofList [ListArithmetic C] {M : AddCommMon C} :
    ofList ≫ bag.aggregator M = list.lift' (M := M.toAddMon) (𝟙 M.X) := by
  sorry

end bag

end CategoryTheory
