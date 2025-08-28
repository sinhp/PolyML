/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monad.Monadicity
import PolyML.Monoidal.ListArithmetic
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
  Mon_Class CommMon_ Monad

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

class WithBags where
  functor : C ⥤ CommMon_ C
  adj : functor ⊣ CommMon_.forget C

variable {C} [WithBags C]

open WithBags

/-- The common monoid structure on `bag A` is given by the free commutative monoid functor. -/
def freeCommMon (A : C) : CommMon_ C := WithBags.functor.obj A

def freeCommMon.lift {A : C} {M : CommMon_ C} (f : A ⟶ M.X) : freeCommMon A ⟶ M :=
  adj.homEquiv A M |>.invFun f

/-- The monoid structure on `bag A`. -/
def bagMon (A : C) : Mon_ C := freeCommMon A |>.toMon_

def bagMon.lift {A : C} {M : CommMon_ C} (f : A ⟶ M.X) : bagMon A ⟶ M.toMon_ :=
  (freeCommMon.lift f) |> (CommMon_.forget₂Mon_ C).map

theorem bagMon.lift_eq_counit_app {M : CommMon_ C} :
    (bagMon.lift (𝟙 M.X)).hom = (adj.counit.app M).hom := by
  sorry

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
theorem braiding_append : (β_ (bag A) (bag A)).hom ≫ append = append := by
  dsimp [bag, append]
  simp only [IsCommMon.mul_comm, forget₂Mon_obj_mul]

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
def lift {M : CommMon_ C} (f : A ⟶ M.X) : bag A ⟶ M.X :=
  bagMon.lift f |> (CommMon_.forget C).map

theorem lift_eq_counit_app {M : CommMon_ C} :
    lift (𝟙 M.X) = (adj.counit.app M).hom := by
  simp [lift, bagMon.lift_eq_counit_app]

theorem one_lift {M : CommMon_ C} {f : A ⟶ M.X} : η ≫ lift f = η := by
  dsimp [lift]
  simp only [IsMon_Hom.one_hom]

theorem mul_lift {M : CommMon_ C} {f : A ⟶ M.X} :  μ ≫ lift f = (lift f ⊗ₘ lift f) ≫ μ := by
  dsimp [lift]
  simp only [IsMon_Hom.mul_hom]

theorem singleton_lift {M : CommMon_ C} {f : A ⟶ M.X} : singleton ≫ lift f = f := by
  dsimp [singleton, lift, bagMon.lift, freeCommMon.lift]
  exact (adj.homEquiv A M).right_inv f

/-- The functorial action of `bag` on morphisms. -/
def map {B : C} (f : A ⟶ B) : bag A ⟶ bag B := bag.endofunctor.map f

theorem map_eq_lift {B : C} (f : A ⟶ B) : map f = lift (f ≫ singleton) := by
  sorry

theorem map_lift_eq_lift_comp {M : CommMon_ C} {B : C} (f : A ⟶ B) (g : B ⟶ M.X) :
    map f ≫ lift g = lift (f ≫ g) := by
  dsimp [lift]
  have := Adjunction.homEquiv_naturality_left_symm (C:=C) (adj) (Y:=M) (X:=B) (X':=A) f g
  dsimp [bagMon.lift, freeCommMon.lift, Adjunction.homEquiv, map, endofunctor]
  simp_all only [map_comp, comp', Category.assoc, Mon_.comp_hom', toMon__X]

@[simp]
theorem nil_map {B : C} {f : A ⟶ B} :
    η ≫ map f = η := by
  rw [map_eq_lift]
  dsimp [lift]
  simp only [IsMon_Hom.one_hom, forget₂Mon_obj_one]

@[simp]
theorem singleton_naturality {B : C} {f : A ⟶ B} :
    singleton ≫ map f = f ≫ singleton := by
  rw [map_eq_lift, singleton_lift]

theorem append_map {B : C} {f : A ⟶ B} : (map f ⊗ₘ map f) ≫ μ = μ ≫ map f := by
  rw [map_eq_lift, mul_lift]

theorem self_tensor_map_self_cons {B : C} {f : A ⟶ B} :
    (f ⊗ₘ map f) ≫ cons = cons ≫ map f := by
  dsimp [cons, append, bag]
  rw [Category.assoc, ← append_map]
  have := singleton_naturality (C:=C) (f:= (map f ⊗ₘ map f))
  rw [← Category.assoc, ← Category.assoc]
  refine ?_ =≫ μ
  sorry

def ofList [ListArithmetic C] : list A ⟶ bag A := list.lift (bag.singleton)

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

end bag

section Monadicity

open Monad Limits

instance hasReflexiveCoequalizersOfMon : HasReflexiveCoequalizers (CommMon_ C) where
  has_coeq {A B} (f g) := by sorry

instance preservesColimitOfIsReflexivePairOfMonForget :
    PreservesColimitOfIsReflexivePair (CommMon_.forget C) where
  out {A B} (f g) r := by sorry

instance :  (CommMon_.forget C).ReflectsIsomorphisms where
  reflects {A B} f is_iso := by sorry

instance monadicRightAdjointOfMonForget : MonadicRightAdjoint (CommMon_.forget C) :=
  monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms <| WithBags.adj

end Monadicity

namespace bag

variable (C)

def monad : Monad C := adj |> Adjunction.toMonad

def commMonToBagAlgebraFunctor : CommMon_ C ⥤ (bag.monad C).Algebra := Monad.comparison _

/-- The equivalence between the category of algebras for the `list` monad and the category of monoids in `C`. -/
instance commMonToBagAlgebraFunctorIsEquivalence : (commMonToBagAlgebraFunctor C).IsEquivalence := by
  refine MonadicRightAdjoint.eqv

variable {C} {A : C}

theorem monad_obj : (monad C).obj A = bag A := rfl

def join : bag (bag A) ⟶ bag A := (monad C).μ.app A

namespace Algebra


/-- A commutative monoid structure on gives rise to an algebra for the `bag` monad. -/
@[simps!]
def ofCommMon (M : CommMon_ C) : (monad C).Algebra := commMonToBagAlgebraFunctor _ |>.obj M

@[simp]
theorem ofMon_a_eq {M : CommMon_ C} : (ofCommMon M).a = bag.lift (𝟙 M.X) := by
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
instance monClassOf (α : Algebra (monad C)) : Mon_Class (α.A) where
  one := nil ≫ α.a
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

def commMonOf (α : Algebra (monad C)) : CommMon_ C where
  X := α.A

noncomputable def commMonToBagAlgebraFunctorIsEquivalence' : (monad C).Algebra ≌ CommMon_ C :=
  (commMonToBagAlgebraFunctor C).asEquivalence.symm

-- SH: an explicit and constructive/computable construction of the equivalence without recourse to the monadicity theorem
def equivalenceMon : (monad C).Algebra ≌ CommMon_ C where
  functor := {
    obj α := ⟨α.A⟩
    map {α α'} f := Mon_.Hom.mk' f.1 (by sorry) (by sorry)
    map_id := sorry
    map_comp := sorry
  }
  inverse := commMonToBagAlgebraFunctor C
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry


end Algebra

open Algebra

def aggregator (M : CommMon_ C) : bag M.X ⟶ M.X := (ofCommMon M).a

section aggregator

variable {M : CommMon_ C}

theorem aggregator_eq_lift : aggregator M = lift (𝟙 M.X) := by
  dsimp [aggregator, ofCommMon, lift]
  simp [commMonToBagAlgebraFunctor, comparison]
  simp only [bagMon.lift_eq_counit_app]

theorem aggregator_one : η ≫ aggregator M = η := by
  dsimp [aggregator, ofCommMon, lift]
  simp only [commMonToBagAlgebraFunctor, comparison]
  simp [IsMon_Hom.one_hom]

theorem aggregator_mul :
    μ ≫ aggregator M = (aggregator M ⊗ₘ aggregator M) ≫ μ := by
  dsimp [aggregator]
  simp only [IsMon_Hom.mul_hom]

theorem aggregator_singleton : singleton ≫ aggregator M = 𝟙 M.X := by
  dsimp [aggregator, ofCommMon, commMonToBagAlgebraFunctor]
  rw [← lift_eq_counit_app, singleton_lift]

theorem aggregator_join : join ≫ aggregator M = (map <| aggregator M) ≫ aggregator M := by
  dsimp [join, aggregator, ofCommMon]
  simp [commMonToBagAlgebraFunctor, comparison]
  simpa using (ofCommMon M).assoc

theorem aggregator_map {M' : CommMon_ C} {f : M.X ⟶ M'.X} :
    map f ≫ aggregator M' = aggregator M ≫ f := by
  sorry

theorem aggregator_ofList [ListArithmetic C] {M' : CommMon_ C} :
    ofList ≫ bag.aggregator M = M.toMon_.aggregator := by
  sorry

end aggregator

end bag

end CategoryTheory
