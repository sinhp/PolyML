/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
import Mathlib.Data.Finsupp.Weight
import PolyML.FreeCommMon

/-
We show that the category of types admit bags construction. In particular,
the left adjoint to the forgetful functor from commutative monoids to types
is given by the multiset functor.
-/

noncomputable section

namespace CategoryTheory

open Category CategoryTheory MonoidalCategory Mon_Class CommMon_ Monad Finsupp Multiset

universe v u

-- #synth CartesianMonoidalCategory (Type u)

-- #check Multiset.toFinsupp

-- variable (α : Type u)

-- def multisetIsoAddMonoidAlgebra [DecidableEq α] : Multiset α ≃+ ℕ[α] :=
--   Multiset.toFinsupp

-- def iso [DecidableEq α] : Multiset α ≃ ℕ[α] := Multiset.toFinsupp.toEquiv


-- attribute [local instance] CommMonTypeEquivalenceCommMon.commMonCommMonoid

-- instance addMonoidOfMonClass (α : Type u) [Mon_Class α] : Monoid α :=
--   MonTypeEquivalenceMon.monMonoid α

-- instance monAddMonoid (α : Type u) [Mon_Class α] : AddMonoid α where
--   add x y := μ[α] (x, y)
--   zero := η[α] PUnit.unit
--   zero_add x := congr_fun (one_mul α) (PUnit.unit, x)
--   add_zero x := congr_fun (mul_one α) (x, PUnit.unit)
--   add_assoc x y z := sorry
--   nsmul := sorry
--   nsmul_zero := sorry
--   nsmul_succ x n := sorry

-- instance monAddCommMonoid (α : Type u) [Mon_Class α] [IsCommMon α] : AddCommMonoid α :=
--   { monAddMonoid α with
--     add_comm := fun x y => congr_fun (IsCommMon.mul_comm α) (y, x) }

instance (β : AddCommMonCat) :  AddCommMonoid ((forget AddCommMonCat).obj β) := β.str

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

namespace bagType

def functor : Type u ⥤ AddCommMonCat where
  obj α := AddCommMonCat.of (α →₀ ℕ)
  map {α β} f := AddCommMonCat.ofHom <| mapDomain.addMonoidHom f

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
    right_inv f := sorry
  }
  homEquiv_naturality_left_symm := sorry
  homEquiv_naturality_right X X' := by {
    simp only [Equiv.coe_fn_mk, AddCommMonCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
      ConcreteCategory.forget_map_eq_coe]
    rfl
  }
}

theorem CommMon_forget_aux :
    CommMon_.forget (Type u) =
    (CommMonTypeEquivalenceCommMon.functor ⋙ AddCommMonCat.equivalence.inverse) ⋙ (forget AddCommMonCat) := by
  rfl

instance withBags : WithBags (Type u) where
  functor := functor ⋙ (AddCommMonCat.equivalence.functor ⋙ CommMonTypeEquivalenceCommMon.inverse)
  adj := by
    rw [CommMon_forget_aux]
    refine Adjunction.comp adjunction ?_
    refine Adjunction.comp AddCommMonCat.equivalence.toAdjunction
      commMonTypeEquivalenceCommMon.symm.toAdjunction

theorem eq_Finsupp (α : Type u) : bag α = (α →₀ ℕ) := by rfl

def equivMultiset (α : Type u) : bag α ≃ Multiset α := by
  have := Classical.decEq α
  exact Multiset.toFinsupp.toEquiv.symm

instance monClassOfAddMonoid (α : Type u) [AddMonoid α] : Mon_Class α where
  one := fun _ => 0
  mul := Add.add.uncurry
  one_mul := by
    ext f
    simp_all only [types_comp_apply, whiskerRight_apply, Function.uncurry_apply_pair]
    apply AddZeroClass.zero_add
  mul_one := sorry
  mul_assoc := by sorry

#check CategoryTheory.braiding_hom_apply

instance isCommMonOfAddCommMonoid (α : Type u) [AddCommMonoid α] : IsCommMon α where
  mul_comm := sorry

def commMonOfAddCommMonoid (α : Type u) [AddCommMonoid α] : CommMon_ (Type u) := ⟨α⟩

theorem aggregator_sum {α : Type u} [AddCommMonoid α] :
    (equivMultiset α).invFun ≫ bag.aggregator (commMonOfAddCommMonoid α) = Multiset.sum (M:= α) := by
  simp [bag.aggregator, bag.algebra.ofCommMon_a]
  ext m
  simp only [types_comp_apply]
  sorry

end bagType

end CategoryTheory
