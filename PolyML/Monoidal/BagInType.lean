/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
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

-- #synth CartesianMonoidalCategory (Type u)

-- #check Multiset.toFinsupp

-- variable (α : Type u)

-- def multisetIsoAddMonoidAlgebra [DecidableEq α] : Multiset α ≃+ ℕ[α] :=
--   Multiset.toFinsupp

-- def iso [DecidableEq α] : Multiset α ≃ ℕ[α] := Multiset.toFinsupp.toEquiv


-- attribute [local instance] CommMonTypeEquivalenceCommMon.commMonCommMonoid

-- instance addMonoidOfMonClass (α : Type u) [MonObj α] : Monoid α :=
--   MonTypeEquivalenceMon.monMonoid α

-- instance monAddMonoid (α : Type u) [MonObj α] : AddMonoid α where
--   add x y := μ[α] (x, y)
--   zero := η[α] PUnit.unit
--   zero_add x := congr_fun (one_mul α) (PUnit.unit, x)
--   add_zero x := congr_fun (mul_one α) (x, PUnit.unit)
--   add_assoc x y z := sorry
--   nsmul := sorry
--   nsmul_zero := sorry
--   nsmul_succ x n := sorry

-- instance monAddCommMonoid (α : Type u) [MonObj α] [IsCommMon α] : AddCommMonoid α :=
--   { monAddMonoid α with
--     add_comm := fun x y => congr_fun (IsCommMon.mul_comm α) (y, x) }

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

theorem aggregator_sum {α : Type u} [AddCommMonoid α] :
    (equivMultiset α).invFun ≫ bag.aggregator (commMonOfAddCommMonoid α) = Multiset.sum (M:= α) := by
  letI : DecidableEq α := Classical.decEq α
  simp [bag.aggregator, bag.Algebra.ofCommMon_a]
  ext m
  simp only [types_comp_apply]

  let M := commMonOfAddCommMonoid α
  let f := (WithBags.adj (C := Type u)).counit.app M
  let F : (α →₀ ℕ) → α := f.hom

  change F (Multiset.toFinsupp m) = Multiset.sum m

  have h_zero : F (0 : α →₀ ℕ) = (0 : α) := by
    have h := bag.one_lift (M := M) (f := 𝟙 α)
    have h_val := congr_fun h PUnit.unit
    simp only [types_comp_apply] at h_val
    dsimp [M, commMonOfAddCommMonoid, monClassOfAddMonoid] at h_val
    exact h_val

  have h_add : ∀ (x y : α →₀ ℕ), F (x + y) = F x + F y := fun x y => by
    have hF : ∀ z, F z = (bag.lift (M := M) (𝟙 α)) z := fun z => by
      dsimp [F, f]
      exact congr_fun bag.lift_eq_counit_app.symm z
    rw [hF (x + y), hF x, hF y]
    have h_val := congr_fun (bag.mul_lift (M := M) (f := 𝟙 α)) (x, y)
    erw [types_comp_apply, types_comp_apply] at h_val
    rw [MonoidalCategory.tensorHom_def] at h_val
    erw [types_comp_apply] at h_val
    erw [whiskerRight_apply, whiskerLeft_apply] at h_val
    dsimp [MonObj.mul, monClassOfAddMonoid, bag.monClass, bag.append, bag, Function.uncurry] at h_val
    exact h_val

  have h_sing : ∀ (x : α), F (Finsupp.single x 1) = x := fun x => by
    have hF : F (Finsupp.single x 1) = (bag.lift (M := M) (𝟙 α)) (Finsupp.single x 1) := by
      dsimp [F, f]
      exact congr_fun bag.lift_eq_counit_app.symm (Finsupp.single x 1)
    rw [hF]
    have h_val := congr_fun (bag.singleton_lift (M := M) (f := 𝟙 α)) x
    erw [types_comp_apply] at h_val
    dsimp [bag.singleton] at h_val
    exact h_val

  induction m using Multiset.induction_on with
  | empty =>
    have h_empty : Multiset.toFinsupp (0 : Multiset α) = 0 := by ext; rfl
    rw [h_empty, Multiset.sum_zero, h_zero]
  | cons a m ih =>
    have h_toFinsupp_cons : Multiset.toFinsupp (a ::ₘ m) = Finsupp.single a 1 + Multiset.toFinsupp m := by
      ext x
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      change Multiset.count x (a ::ₘ m) = (if a = x then 1 else 0) + Multiset.count x m
      rw [Multiset.count_cons]
      by_cases h : a = x
      · subst h
        simp [add_comm]
      · simp [h, Ne.symm h]
    rw [h_toFinsupp_cons, Multiset.sum_cons]
    rw [h_add, h_sing, ih]

end bagType

end CategoryTheory
