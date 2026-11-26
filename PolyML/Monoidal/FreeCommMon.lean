/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monad.Monadicity
import PolyML.Monoidal.List
import PolyML.Monoidal.FreeMon


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
  MonObj CommMon Monad

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

class WithBags where
  functor : C ⥤ CommMon C
  adj : functor ⊣ CommMon.forget C

variable {C} [WithBags C]

open WithBags

/-- The common monoid structure on `bag A` is given by the free commutative monoid functor. -/
def freeCommMon (A : C) : CommMon C := WithBags.functor.obj A

def freeCommMon.lift {A : C} {M : CommMon C} (f : A ⟶ M.X) : freeCommMon A ⟶ M :=
  adj.homEquiv A M |>.invFun f

/-- The monoid structure on `bag A`. -/
def bagMon (A : C) : Mon C := freeCommMon A |>.toMon

def bagMon.lift {A : C} {M : CommMon C} (f : A ⟶ M.X) : bagMon A ⟶ M.toMon :=
  (freeCommMon.lift f) |> (CommMon.forget₂Mon C).map

theorem bagMon.lift_eq_counit_app {M : CommMon C} :
    (bagMon.lift (𝟙 M.X)).hom = (adj.counit.app M).hom := by
  dsimp [bagMon.lift, freeCommMon.lift, Adjunction.homEquiv]
  rw [Functor.map_id]
  change 𝟙 _ ≫ (adj.counit.app M).hom = _
  rw [Category.id_comp]

/-- The underlying type of the free commutative monoid on `A`. -/
abbrev bag (A : C) : C := bagMon A |>.X

namespace bag

variable {A : C}

def endofunctor : C ⥤ C :=
  WithBags.functor ⋙ CommMon.forget C

instance monClass : MonObj (bag A) := bagMon A |> Mon.mon

instance isCommMonObj : IsCommMonObj (bag A) := freeCommMon A |> CommMon.comm

def nil : 𝟙_C ⟶ bag A := η

def append : bag A ⊗ bag A ⟶ bag A := μ

/-- `append` is symmetric because for bags. -/
@[reassoc (attr := simp)]
theorem braiding_append : (β_ (bag A) (bag A)).hom ≫ append = append := by
  dsimp [bag, append]
  simp only [IsCommMonObj.mul_comm, forget₂Mon_obj_mul]

def singleton : A ⟶ bag A := adj.unit.app A

def cons : A ⊗ bag A ⟶ bag A := (singleton ▷ bag A) ≫ append

def snoc : bag A ⊗ A ⟶ bag A := (bag A ◁ singleton) ≫ append

/-- Appending an element as head or tail is the same operation for bags. -/
theorem braiding_snoc_eq_cons : (β_ A (bag A)).hom ≫ snoc = cons := by
  dsimp [cons, snoc]
  nth_rw 2 [← braiding_append]
  simp only [BraidedCategory.braiding_naturality_left_assoc]

/-- Given a commutative monoid object `M` in `C`, this lifts
`f : A ⟶ M.X` to a morphism from `bag A` to `M.X`. -/
def lift {M : CommMon C} (f : A ⟶ M.X) : bag A ⟶ M.X :=
  bagMon.lift f |> (CommMon.forget C).map

theorem lift_eq_counit_app {M : CommMon C} :
    lift (𝟙 M.X) = (adj.counit.app M).hom := by
  simp [lift, bagMon.lift_eq_counit_app]

theorem one_lift {M : CommMon C} {f : A ⟶ M.X} : η ≫ lift f = η := by
  dsimp [lift]
  simp only [IsMonHom.one_hom]

theorem mul_lift {M : CommMon C} {f : A ⟶ M.X} :  μ ≫ lift f = (lift f ⊗ₘ lift f) ≫ μ := by
  dsimp [lift]
  simp only [IsMonHom.mul_hom]

theorem singleton_lift {M : CommMon C} {f : A ⟶ M.X} : singleton ≫ lift f = f := by
  dsimp [singleton, lift, bagMon.lift, freeCommMon.lift]
  exact (adj.homEquiv A M).right_inv f

/-- The functorial action of `bag` on morphisms. -/
def map {B : C} (f : A ⟶ B) : bag A ⟶ bag B := bag.endofunctor.map f

theorem map_eq_lift {B : C} (f : A ⟶ B) : map f = lift (f ≫ singleton) := by
  show (functor.map f).hom = (freeCommMon.lift (f ≫ singleton)).hom
  congr 1
  show functor.map f = freeCommMon.lift (f ≫ singleton)
  show functor.map f = (adj.homEquiv A (freeCommMon B)).invFun (f ≫ singleton)
  rw [show (adj.homEquiv A (freeCommMon B)).invFun = (adj.homEquiv A (freeCommMon B)).symm from rfl]
  apply (adj.homEquiv A (freeCommMon B)).eq_symm_apply.mpr
  show adj.unit.app A ≫ (CommMon.forget C).map (functor.map f) = f ≫ adj.unit.app B
  exact (adj.unit.naturality f).symm

theorem map_lift_eq_lift_comp {M : CommMon C} {B : C} (f : A ⟶ B) (g : B ⟶ M.X) :
    map f ≫ lift g = lift (f ≫ g) := by
  dsimp [lift]
  have := Adjunction.homEquiv_naturality_left_symm (C:=C) (adj) (Y:=M) (X:=B) (X':=A) f g
  dsimp [bagMon.lift, freeCommMon.lift, Adjunction.homEquiv, map, endofunctor]
  simp_all only [map_comp, comp', Category.assoc, Mon.comp_hom', toMon_X]

@[simp]
theorem nil_map {B : C} {f : A ⟶ B} :
    η ≫ map f = η := by
  rw [map_eq_lift]
  dsimp [lift]
  simp only [IsMonHom.one_hom, forget₂Mon_obj_one]

@[simp]
theorem singleton_naturality {B : C} {f : A ⟶ B} :
    singleton ≫ map f = f ≫ singleton := by
  rw [map_eq_lift, singleton_lift]

theorem append_map {B : C} {f : A ⟶ B} : (map f ⊗ₘ map f) ≫ μ = μ ≫ map f := by
  rw [map_eq_lift, mul_lift]

theorem self_tensor_map_self_cons {B : C} {f : A ⟶ B} :
    (f ⊗ₘ map f) ≫ cons = cons ≫ map f := by
  dsimp [cons, append]
  rw [Category.assoc, ← append_map, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [tensorHom_def, Category.assoc, whisker_exchange, ← Category.assoc,
    ← comp_whiskerRight, ← singleton_naturality, comp_whiskerRight, Category.assoc,
    ← tensorHom_def]

def ofList [ListArithmetic C] : list A ⟶ bag A := list.lift (bag.singleton)

theorem ofList_nil [ListArithmetic C] :
    list.nil ≫ ofList = bag.nil (A:= A) := by
  simp only [bag.nil, ofList, singleton, list.nil, list.lift,list.foldr]
  simp only [plist.nil_rc]

theorem ofList_cons [ListArithmetic C] :
    list.cons ≫ ofList = A ◁ ofList ≫ bag.cons := by
  dsimp [ofList, list.lift, list.foldr, list.cons]
  rw [plist.cons_rc]
  rfl

/-
TODO: show that `ofList` is a quotient morphism. The relation should be thought of as
the permutation relation on lists, i.e. `l1 ~ l2` if `l1` can be obtained from `l2` by permuting the elements.

Tip: can we show for instance that this map is an effective epi? If so, every effective epi is regular and therefore W is `perm` relation.
-/

end bag

section Monadicity

open Monad Limits

instance hasReflexiveCoequalizersOfMon : HasReflexiveCoequalizers (CommMon C) where
  has_coeq {A B} (f g) := by sorry

instance preservesColimitOfIsReflexivePairOfMonForget :
    PreservesColimitOfIsReflexivePair (CommMon.forget C) where
  out {A B} (f g) r := by sorry

instance :  (CommMon.forget C).ReflectsIsomorphisms where
  reflects {A B} f is_iso := by sorry

instance monadicRightAdjointOfMonForget : MonadicRightAdjoint (CommMon.forget C) :=
  monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms <| WithBags.adj

end Monadicity

namespace bag

variable (C)

def monad : Monad C := adj |> Adjunction.toMonad

def commMonToBagAlgebraFunctor : CommMon C ⥤ (bag.monad C).Algebra := Monad.comparison _

/-- The equivalence between the category of algebras for the `list` monad and the category of monoids in `C`. -/
instance commMonToBagAlgebraFunctorIsEquivalence : (commMonToBagAlgebraFunctor C).IsEquivalence := by
  refine MonadicRightAdjoint.eqv

variable {C} {A : C}

theorem monad_obj : (monad C).obj A = bag A := rfl

def join : bag (bag A) ⟶ bag A := (monad C).μ.app A

namespace Algebra

/-- A commutative monoid structure on gives rise to an algebra for the `bag` monad. -/
@[simps!]
def ofCommMon (M : CommMon C) : (monad C).Algebra := commMonToBagAlgebraFunctor _ |>.obj M

@[simp]
theorem ofMon_a_eq {M : CommMon C} : (ofCommMon M).a = bag.lift (𝟙 M.X) := by
  dsimp [ofCommMon, commMonToBagAlgebraFunctor, Monad.comparison]
  have := CategoryTheory.Adjunction.unit_comp_map_eq_iff (C:=C)
     (adj) (A:=M.X) (B:=M) (f:= (bagMon.lift (𝟙 M.X))) (𝟙 M.X)
  dsimp [monad, lift]
  simp only [Functor.map_id, id_comp] at this
  symm
  congr
  apply this.mp
  simpa using singleton_lift

/-- An algebra for the `bag` monad is a commutative monoid structure. -/
instance monClassOf (α : Algebra (monad C)) : MonObj (α.A) where
  one := nil ≫ α.a
  mul := (singleton ⊗ₘ singleton) ≫ μ ≫ α.a
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry

instance isCommMonObj {α : Algebra (monad C)} : IsCommMonObj (α.A) where
  mul_comm := by
    dsimp [MonObj.mul]
    rw [tensorHom_def', ← Category.assoc]
    rw [← BraidedCategory.braiding_naturality_left_assoc]
    rw [← BraidedCategory.braiding_naturality_right]
    rw [Category.assoc, Category.assoc]
    simp only [IsCommMonObj.mul_comm_assoc, forget₂Mon_obj_mul, Category.assoc]
    exact Eq.symm (whisker_exchange_assoc singleton singleton (μ ≫ α.a))

def commMon (α : (monad C).Algebra) : CommMon C where
  X := α.A

/-- The functor from algebras for the `bag` monad to commutative monoid objects. -/
def algebraToCommMon : (monad C).Algebra ⥤ CommMon C where
  obj α := commMon α
  map {α α'} f := Mon.Hom.mk' f.1 (by sorry) (by sorry)
  map_id _ := rfl
  map_comp {α α' α''} f g := by
    ext
    rfl

/-- Explicit, constructive equivalence between `bag`-monad algebras and commutative monoids in `C`. -/
def equivalenceMon : (monad C).Algebra ≌ CommMon C where
  functor := algebraToCommMon
  inverse := commMonToBagAlgebraFunctor C
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

end Algebra

open Algebra

def aggregator (M : CommMon C) : bag M.X ⟶ M.X := (ofCommMon M).a

section aggregator

variable {M : CommMon C}

theorem aggregator_eq_lift : aggregator M = lift (𝟙 M.X) := by
  dsimp [aggregator, ofCommMon, lift]
  simp [commMonToBagAlgebraFunctor, comparison]
  simp only [bagMon.lift_eq_counit_app]

theorem aggregator_one : η ≫ aggregator M = η := by
  dsimp [aggregator, ofCommMon, lift]
  simp only [commMonToBagAlgebraFunctor, comparison]
  simp [IsMonHom.one_hom]

theorem aggregator_mul :
    μ ≫ aggregator M = (aggregator M ⊗ₘ aggregator M) ≫ μ := by
  dsimp [aggregator]
  simp only [IsMonHom.mul_hom]

theorem aggregator_singleton : singleton ≫ aggregator M = 𝟙 M.X := by
  dsimp [aggregator, ofCommMon, commMonToBagAlgebraFunctor]
  rw [← lift_eq_counit_app, singleton_lift]

theorem aggregator_join : join ≫ aggregator M = (map <| aggregator M) ≫ aggregator M := by
  dsimp [join, aggregator, ofCommMon]
  simp [commMonToBagAlgebraFunctor, comparison]
  simpa using (ofCommMon M).assoc

/-- Aggregator is natural with respect to commutative monoid homomorphisms. -/
theorem aggregator_map' {M' : CommMon C} {f : M ⟶ M'} :
    map f.hom ≫ aggregator M' = aggregator M ≫ f.hom := by
  have := (WithBags.adj.counit.naturality (X := M) (Y := M') f)
  have h_nat_hom := congr_arg (fun g => g.hom) this
  simp only [Functor.comp_map, Functor.id_map] at h_nat_hom
  show map f.hom ≫ (WithBags.adj.counit.app M').hom =
    (WithBags.adj.counit.app M).hom ≫ f.hom
  exact h_nat_hom

theorem aggregator_map {M' : CommMon C} {f : M.X ⟶ M'.X} [IsMonHom f] :
    map f ≫ aggregator M' = aggregator M ≫ f :=
  aggregator_map' (M := M) (M' := M') (f := ⟨f⟩)

theorem aggregator_ofList [ListArithmetic C] :
    ofList ≫ bag.aggregator M = M.toMon.aggregator := by
  have hMon : IsMonHom (bag.aggregator M) :=
    ⟨bag.aggregator_one, bag.aggregator_mul⟩
  let g : bagMon M.X ⟶ M.toMon := Mon.Hom.mk' (bag.aggregator M)
  have hcomp : list.lift (bag.singleton (A := M.X)) ≫ bag.aggregator M =
      list.lift (M := M.toMon) (bag.singleton (A := M.X) ≫ bag.aggregator M) := by
    have hnat := ((list.freeMonForgetAdjunction C).homEquiv_naturality_right_symm
      (X := M.X) (Y := bagMon M.X) (Y' := M.toMon) bag.singleton g)
    have h_hom := congr_arg Mon.Hom.hom hnat
    simp only [Mon.comp_hom', list.freeMonForgetAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
      list.homEquiv, Equiv.coe_fn_symm_mk, Mon.Hom.mk'] at h_hom
    exact h_hom.symm
  show list.lift bag.singleton ≫ bag.aggregator M = M.toMon.aggregator
  rw [hcomp, bag.aggregator_singleton]
  show list.lift (𝟙 M.X) = M.toMon.aggregator
  exact (list.Algebra.ofMon_a_eq (C := C) (M := M.toMon)).symm

end aggregator

end bag

end CategoryTheory
