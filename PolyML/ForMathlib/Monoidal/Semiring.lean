/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Distributive.Monoidal
import PolyML.ForMathlib.Monad.Distrib
import PolyML.ForMathlib.Monoidal.AddCommMon_

/-!
# Internal Semiring Objects and The Equivalence with Algebras of the Lifted Bag Monad
-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory ComonObj Monad DistribLaw

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]

attribute [local instance] AddMonObj.fromMonObj

attribute [local instance] IsAddCommMon.fromIsCommMon

/-- Syntactic transfer of a commutative monoid to an additive commutative monoid. -/
def AddCommMon.fromCommMon (M : CommMon C) : AddCommMon C where
  X := M.X
  mon := @AddMonObj.fromMonObj _ _ _ _ M.mon

class DistribObj (X : C) [ComonObj X] extends MonObj X, AddMonObj X where
  left_distrib : Δ ▷ (X ⊗ X) ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ add = X ◁ add ≫ mul
  right_distrib : (X ⊗ X) ◁ Δ ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ add = add ▷ X ≫ mul

class LeftDistribObj (X : C) [ComonObj X] extends MonObj X, AddMonObj X where
  left_distrib : Δ ▷ (X ⊗ X) ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ add = X ◁ add ≫ mul

class RightDistribObj (X : C) [ComonObj X] extends MonObj X, AddMonObj X where
  right_distrib : (X ⊗ X) ◁ Δ ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ add = add ▷ X ≫ mul

alias mul_add := left_distrib

alias add_mul := right_distrib

instance (priority := 100) DistribObj.leftDistribClass (X : C) [ComonObj X] [DistribObj X] :
    LeftDistribObj X :=
  ⟨DistribObj.left_distrib⟩

instance (priority := 100) DistribObj.rightDistribClass (X : C) [ComonObj X] [DistribObj X] :
    RightDistribObj X :=
  ⟨DistribObj.right_distrib⟩

namespace DistribObj

attribute [local instance] instTensorUnit

instance : DistribObj (𝟙_ C) where
  left_distrib := by
    show (λ_ _).inv ▷ ((𝟙_ C) ⊗ (𝟙_ C)) ≫ tensorμ ..
        ≫ ((λ_ _).hom ⊗ₘ (λ_ _).hom) ≫ (λ_ _).hom = (𝟙_ C) ◁ (λ_ _).hom ≫ (λ_ _).hom
    rw [tensorμ, braiding_tensorUnit_left]
    monoidal
  right_distrib := by
    show ((𝟙_ C) ⊗ (𝟙_ C)) ◁ (λ_ _).inv ≫ tensorμ ..
        ≫ ((λ_ _).hom ⊗ₘ (λ_ _).hom) ≫ (λ_ _).hom = (λ_ _).hom ▷ (𝟙_ C) ≫ (λ_ _).hom
    rw [tensorμ, braiding_tensorUnit_left]
    monoidal

end DistribObj

class SemiringObj (X : C) extends ComonObj X, AddMonObj X, IsAddCommMonObj X, MonObj X,
    DistribObj X where
  zero_mul : zero ▷ X ≫ mul = (𝟙_ C) ◁ ε ≫ (λ_ _).hom ≫ zero
  mul_zero : X ◁ zero ≫ mul = ε ▷ (𝟙_ C) ≫ (ρ_ _).hom ≫ zero

namespace SemiringObj

-- @[simps]
-- instance : SemiringObj (𝟙_ C) where
--   zero_mul := by sorry
--   mul_zero := by sorry

end SemiringObj

section IsSemiring_Hom

open scoped SemiringObj

variable {M N O : C} [SemiringObj M] [SemiringObj N] [SemiringObj O]

/-- The property that a morphism between monoid objects is a monoid morphism. -/
class IsSemiring_Hom (f : M ⟶ N) extends IsComonHom f, IsAddMonHom f, IsMonHom f

instance : IsSemiring_Hom (𝟙 M) where

instance (f : M ⟶ N) (g : N ⟶ O) [IsSemiring_Hom f] [IsSemiring_Hom g] : IsSemiring_Hom (f ≫ g) where

instance (f : M ≅ N) [IsSemiring_Hom f.hom] : IsSemiring_Hom f.inv where

end IsSemiring_Hom


attribute [local instance] ComonObj.instTensorUnit in
instance : SemiringObj (𝟙_ C) where
  zero_mul := by
    show (𝟙 (𝟙_ C)) ▷ (𝟙_ C) ≫ (λ_ _).hom = (𝟙_ C) ◁ (𝟙 (𝟙_ C)) ≫ (λ_ _).hom ≫ (𝟙 (𝟙_ C))
    monoidal
  mul_zero := by
    show (𝟙_ C) ◁ (𝟙 (𝟙_ C)) ≫ (λ_ _).hom = (𝟙 (𝟙_ C)) ▷ (𝟙_ C) ≫ (ρ_ _).hom ≫ (𝟙 (𝟙_ C))
    monoidal

variable (C) in
/-- A semiring object internal to a monoidal category.
-/
structure Semiring where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [semiring : SemiringObj X]

attribute [instance] Semiring.semiring

namespace Semiring

variable (C) in
/-- The trivial monoid object. We later show this is initial in `AddMon_ C`.
-/
@[simps!]
def trivial : Semiring C := mk (𝟙_ C)

instance : Inhabited (Semiring C) :=
  ⟨trivial C⟩

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : Semiring C) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [is_semiring_Hom : IsSemiring_Hom hom]

attribute [instance] Hom.is_semiring_Hom

/-- The identity morphism on a monoid object. -/
@[simps]
def id (M : Semiring C) : Hom M M := ⟨𝟙 M.X⟩

instance homInhabited (M : Semiring C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Semiring C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom
  is_semiring_Hom := instIsSemiring_HomComp f.hom g.hom

instance : Category (Semiring C) where
  Hom M N := Hom M N
  id := id
  comp := comp

end Semiring

namespace AlgebraOfLiftingBagtoListAlgebraMonad

open Lift

variable [ListArithmetic C] [WithBags C] (α : Lift.monad (list.monad C) (bag.monad C) |>.Algebra)

/-- The list algebra coming from the algebra of the bag monad lifted to the category of algebras of
the list monad. -/
def listAlgebra : (list.monad C).Algebra := fstAlg α

/-- The bag algebra coming from the algebra of the bag monad lifted to the the category of algebras of
the list monad. -/
def bagAlgebra : (bag.monad C).Algebra := sndAlg α

/-- The monoid object associated to a list algebra. -/
def mon : Mon C := list.Algebra.mon (listAlgebra α)

instance monClass : MonObj α.A.A := list.Algebra.monClass (listAlgebra α)

/-- The commutative monoid object associated to a bag algebra. -/
def commMon : CommMon C := bag.Algebra.commMon (bagAlgebra α)

/-- The additive commutative monoid object associated to a bag algebra.
This is a syntactic copy of `commMon`. -/
def addCommMon : AddCommMon C := AddCommMon.fromCommMon (commMon α)

instance addMonClass : AddMonObj α.A.A := (addCommMon α).toAddMon |>.addMon

instance : IsAddCommMonObj α.A.A := addCommMon α |>.comm

/-- The internal semiring object associated to an algebra of the lifted bag monad to the category
of algebras of the list monad. -/
def toSemiring [SemiCartesianMonoidalCategory C] : Semiring C where
  X := α.A.A
  semiring :=
    { toComonObj := sorry
      toDistribObj := sorry
      zero_mul := by
        sorry
      mul_zero := by
        sorry }

/-- The equivalence of category of algebras of the lifted bag monad and the category of semiring objects. -/
def liftListBagAlgebraSemiringEquivalence [SemiCartesianMonoidalCategory C] :
    (Lift.monad (list.monad C) (bag.monad C)).Algebra ≌ Semiring C where
  functor := {
    obj α := toSemiring α
    map {α β} f := {
      hom := sorry
      is_semiring_Hom := sorry
    }
    map_id X := by
      sorry
    map_comp := by
      sorry
  }
  inverse := sorry
  unitIso := by
    sorry
  counitIso := by
    sorry
  functor_unitIso_comp := by
    sorry

end AlgebraOfLiftingBagtoListAlgebraMonad

end CategoryTheory
