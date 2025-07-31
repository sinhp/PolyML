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

namespace CategoryTheory

open Category CategoryTheory MonoidalCategory Mon_Class CommMon_ Monad Finsupp Multiset

universe v u

-- #synth CartesianMonoidalCategory (Type u)

-- #check Multiset.toFinsupp

-- variable (α : Type u)

-- def multisetIsoAddMonoidAlgebra [DecidableEq α] : Multiset α ≃+ ℕ[α] :=
--   Multiset.toFinsupp

-- def iso [DecidableEq α] : Multiset α ≃ ℕ[α] := Multiset.toFinsupp.toEquiv

-- instance monClassOfAddMonoid (α : Type u) [AddMonoid α] : Mon_Class α where
--   one := fun _ => 0
--   mul := Add.add.uncurry
--   one_mul := sorry
--   mul_one := sorry
--   mul_assoc := sorry

-- instance isCommMonOfAddCommMonoid (α : Type u) [AddCommMonoid α] :  IsCommMon α where
--   mul_comm := sorry

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

noncomputable
def functor : Type u ⥤ AddCommMonCat where
  obj α := AddCommMonCat.of (α →₀ ℕ)
  map {α β} f := AddCommMonCat.ofHom <| mapDomain.addMonoidHom f

noncomputable
def adjunction : functor ⊣  forget AddCommMonCat := Adjunction.mkOfHomEquiv {
  homEquiv α β := {
    toFun f a := f.hom (single a 1)
    invFun g := AddCommMonCat.ofHom (Finsupp.weight (M:= _) (R:= ℕ) g)
    left_inv := sorry
    right_inv := sorry
  }
  homEquiv_naturality_left_symm := sorry
  homEquiv_naturality_right := sorry
}

theorem CommMon_forget_aux :
    CommMon_.forget (Type u) =
    (CommMonTypeEquivalenceCommMon.functor ⋙ AddCommMonCat.equivalence.inverse) ⋙ (forget AddCommMonCat) := by
  rfl

noncomputable
instance : WithBags (Type u) where
  functor := functor ⋙ (AddCommMonCat.equivalence.functor ⋙ CommMonTypeEquivalenceCommMon.inverse)
  adj := by
    rw [CommMon_forget_aux]
    refine Adjunction.comp adjunction ?_
    refine Adjunction.comp AddCommMonCat.equivalence.toAdjunction
      commMonTypeEquivalenceCommMon.symm.toAdjunction

def equivMultiset (α : Type u) [DecidableEq α] : bag α ≃ Multiset α :=
  Multiset.toFinsupp.toEquiv.symm

end bagType

end CategoryTheory
