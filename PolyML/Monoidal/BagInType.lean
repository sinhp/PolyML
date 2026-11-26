/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Weight
import PolyML.Monoidal.FreeCommMon
-- import PolyML.Deprecated.Cartesian.FreeCommMon

/-
We show that the category of types admit bags construction. In particular,
the left adjoint to the forgetful functor from commutative monoids to types
is given by the multiset functor.
-/

noncomputable section

namespace CategoryTheory

open Category CategoryTheory MonoidalCategory MonObj CommMon Monad Finsupp Multiset

universe v u

instance (β : AddCommMonCat) :  AddCommMonoid <| (forget AddCommMonCat).obj β := β.str

namespace bagType

def functor : Type u ⥤ AddCommMonCat where
  obj α := AddCommMonCat.of (α →₀ ℕ)
  map {α β} f := AddCommMonCat.ofHom <| mapDomain.addMonoidHom f

open LinearMap CommMonCat

def adjunction : functor ⊣ forget AddCommMonCat := Adjunction.mkOfHomEquiv {
  homEquiv α β := {
    toFun f a := f.hom (single a 1)
    invFun g := AddCommMonCat.ofHom (Finsupp.weight (M:= _) (R:= ℕ) g)
    left_inv f := by {
      ext g
      simp only [AddCommMonCat.hom_ofHom, AddMonoidHom.coe_comp, Function.comp_apply,
        singleAddHom_apply]
      congr 1
      unfold weight
      ext l
      simp only [AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, Function.comp_apply,
        singleAddHom_apply, linearCombination_single, one_smul]
      rfl
    }
    right_inv f := by {
      ext g
      simp only [AddCommMonCat.hom_ofHom]
      unfold weight
      have : (linearCombination ℕ f).toAddMonoidHom (single g 1)=
       (linearCombination ℕ f) (single g 1) := by {
        simp only [toAddMonoidHom_coe, linearCombination_single, one_smul]}
      rw [linearCombination_single] at this
      simp only [one_smul] at this
      exact this
    }
  }
  homEquiv_naturality_left_symm := by {
    intros X X' Y f g
    simp only [Equiv.coe_fn_symm_mk]
    ext h
    unfold weight
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, singleAddHom_apply]
    unfold functor
    simp_all only [AddCommMonCat.hom_comp,
      AddCommMonCat.hom_ofHom, AddMonoidHom.coe_comp, Function.comp_apply, mapDomain.addMonoidHom_apply,
      mapDomain_single]
    have h1 : (linearCombination ℕ (f ≫ g)).toAddMonoidHom (single h 1) =
      (linearCombination ℕ g).toAddMonoidHom (single (f h) 1) := by {
        simp only [toAddMonoidHom_coe, linearCombination_single, types_comp_apply, one_smul]}
    exact h1
  }
  homEquiv_naturality_right X X' := by {
    simp only [Equiv.coe_fn_mk, AddCommMonCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
      ConcreteCategory.forget_map_eq_coe]
    rfl
  }
}

theorem CommMon_forget_aux :
    CommMon.forget (Type u) =
    (CommMonTypeEquivalenceCommMon.functor ⋙ AddCommMonCat.equivalence.inverse) ⋙ (forget AddCommMonCat) := by
  rfl

instance withBags : WithBags (Type u) where
  functor := functor ⋙ (AddCommMonCat.equivalence.functor ⋙ CommMonTypeEquivalenceCommMon.inverse)
  adj := by
    rw [CommMon_forget_aux]
    refine Adjunction.comp adjunction ?_
    refine Adjunction.comp AddCommMonCat.equivalence.toAdjunction
      commMonTypeEquivalenceCommMon.symm.toAdjunction

theorem eq_Finsupp (α : Type u) : bag α = (α →₀ ℕ) := by
  rfl

def equivMultiset (α : Type u) : bag α ≃ Multiset α := by
  have := Classical.decEq α
  exact Multiset.toFinsupp.toEquiv.symm

instance monClassOfAddMonoid (α : Type u) [AddMonoid α] : MonObj α where
  one := fun _ => 0
  mul := Add.add.uncurry
  one_mul := by
    ext f
    simp_all only [types_comp_apply, whiskerRight_apply, Function.uncurry_apply_pair]
    apply AddZeroClass.zero_add
  mul_one := by
    ext f
    simp only [types_comp_apply, whiskerLeft_apply, Function.uncurry_apply_pair]
    apply AddZeroClass.add_zero
  mul_assoc := by
    ext f
    simp only [types_comp_apply, whiskerRight_apply, Function.uncurry_apply_pair, whiskerLeft_apply,
      associator_hom_apply_1]
    apply AddSemigroup.add_assoc

instance isCommMonOfAddCommMonoid (α : Type u) [AddCommMonoid α] : IsCommMonObj α where
  mul_comm := by
    ext f
    simp only [types_comp_apply]
    dsimp [MonObj.mul]
    unfold Function.uncurry
    apply AddCommMonoid.add_comm

def commMonOfAddCommMonoid (α : Type u) [AddCommMonoid α] : CommMon (Type u) := ⟨α⟩

private lemma weight_id_single_add {α : Type u} [AddCommMonoid α]
    (a : α) (n : ℕ) (f : α →₀ ℕ) :
    weight (M := α) (R := ℕ) (fun x : α => x) (single a n + f) =
      n • a + weight (M := α) (R := ℕ) (fun x : α => x) f := by
  rw [AddMonoidHom.map_add (weight (M := α) (R := ℕ) (fun x : α => x)), weight_single]

private theorem weight_id_toMultiset {α : Type u} [AddCommMonoid α] [DecidableEq α]
    (f : α →₀ ℕ) :
    weight (M := α) (R := ℕ) (fun x : α => x) f = (Finsupp.toMultiset f).sum := by
  refine f.induction ?_ ?_
  · simp [weight_apply, toMultiset_zero, Multiset.sum_zero]
  · intro a n f _ _ ih
    rw [weight_id_single_add, toMultiset_add, Multiset.sum_add, toMultiset_single, ih]
    simp [Multiset.sum_nsmul, Multiset.sum_singleton]

private theorem weight_id_toFinsupp_sum {α : Type u} [AddCommMonoid α] [DecidableEq α]
    (s : Multiset α) :
    weight (M := α) (R := ℕ) (fun x : α => x) (Multiset.toFinsupp s) = s.sum := by
  rw [weight_id_toMultiset, Multiset.toFinsupp_toMultiset]

private lemma aggregator_map_add {α : Type u} [AddCommMonoid α] (f g : α →₀ ℕ) :
    bag.aggregator (commMonOfAddCommMonoid α) (@Add.add (α →₀ ℕ) _ f g) =
      @Add.add α _ (bag.aggregator (commMonOfAddCommMonoid α) f)
        (bag.aggregator (commMonOfAddCommMonoid α) g) := by
  have hmul := bag.aggregator_mul (M := commMonOfAddCommMonoid α)
  have key := congrArg (fun φ => φ (f, g)) hmul
  simp [types_comp_apply, whiskerRight_apply, whiskerLeft_apply,
    Function.uncurry_apply_pair] at key
  exact key

private lemma aggregator_apply_single {α : Type u} [AddCommMonoid α] (a : α) :
    bag.aggregator (commMonOfAddCommMonoid α) (single a 1) = a := by
  have hsingle := bag.aggregator_singleton (M := commMonOfAddCommMonoid α)
  rw [show single a 1 = bag.singleton (A := α) a from rfl]
  simpa [types_comp_apply] using congrFun hsingle a

private lemma aggregator_apply_single_nsmul {α : Type u} [AddCommMonoid α] (a : α) (n : ℕ) :
    bag.aggregator (commMonOfAddCommMonoid α) (single a n) = n • a := by
  induction n with
  | zero =>
    simp only [single_zero, zero_smul]
    have h := bag.aggregator_one (M := commMonOfAddCommMonoid α)
    simpa [types_comp_apply, whiskerRight_apply] using
      show bag.aggregator (commMonOfAddCommMonoid α) (0 : α →₀ ℕ) = (0 : α) from
        congrArg (fun f => f PUnit.unit) h
  | succ n ih =>
    rw [show single a (n + 1) = @Add.add (α →₀ ℕ) _ (single a n) (single a 1) from
      single_add a n 1]
    rw [aggregator_map_add, ih, aggregator_apply_single]
    exact (succ_nsmul a n).symm

private theorem aggregator_apply_weight {α : Type u} [AddCommMonoid α] [DecidableEq α]
    (f : α →₀ ℕ) :
    bag.aggregator (commMonOfAddCommMonoid α) f =
      weight (M := α) (R := ℕ) (fun x : α => x) f := by
  refine f.induction ?_ ?_
  · have h := bag.aggregator_one (M := commMonOfAddCommMonoid α)
    have h0 : bag.aggregator (commMonOfAddCommMonoid α) (0 : α →₀ ℕ) = (0 : α) :=
      congrArg (fun f => f PUnit.unit) h
    simp [weight_apply, h0]
  · intro a n f _ _ ih
    rw [show single a n + f = @Add.add (α →₀ ℕ) _ (single a n) f from rfl,
      aggregator_map_add, ih, aggregator_apply_single_nsmul a n]
    exact (weight_id_single_add a n f).symm

theorem aggregator_sum {α : Type u} [AddCommMonoid α] :
    (equivMultiset α).invFun ≫ bag.aggregator (commMonOfAddCommMonoid α) = Multiset.sum (M:= α) := by
  classical
  funext s
  rw [types_comp_apply, equivMultiset, Equiv.invFun_as_coe, Equiv.symm_symm,
    AddEquiv.toEquiv_eq_coe, aggregator_apply_weight]
  simpa [eq_Finsupp α] using weight_id_toFinsupp_sum s


end bagType

end CategoryTheory
