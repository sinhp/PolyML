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

/-- Syntactic transfer of a commutative monoid to an additive commutative monoid. -/
def AddCommMon_.fromCommMon_ (M : CommMon C) : AddCommMon_ C where
  X := M.X
  mon := @AddMon_Class.fromMon_Class _ _ _ _ M.mon

class Distrib_Class (X : C) [ComonObj X] extends MonObj X, AddMon_Class X where
  left_distrib : Δ ▷ (X ⊗ X) ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ add = X ◁ add ≫ mul
  right_distrib : (X ⊗ X) ◁ Δ ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ add = add ▷ X ≫ mul

class LeftDistrib_Class (X : C) [ComonObj X] extends MonObj X, AddMon_Class X where
  left_distrib : Δ ▷ (X ⊗ X) ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ add = X ◁ add ≫ mul

class RightDistrib_Class (X : C) [ComonObj X] extends MonObj X, AddMon_Class X where
  right_distrib : (X ⊗ X) ◁ Δ ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ add = add ▷ X ≫ mul

alias mul_add := left_distrib

alias add_mul := right_distrib

instance (priority := 100) Distrib_Class.leftDistribClass (X : C) [ComonObj X] [Distrib_Class X] :
    LeftDistrib_Class X :=
  ⟨Distrib_Class.left_distrib⟩

instance (priority := 100) Distrib_Class.rightDistribClass (X : C) [ComonObj X] [Distrib_Class X] :
    RightDistrib_Class X :=
  ⟨Distrib_Class.right_distrib⟩

namespace Distrib_Class

--why is Lean asking for this?
instance comonObjUnit : ComonObj (𝟙_ C) := sorry

instance : Distrib_Class (𝟙_ C) where
  left_distrib := sorry
  right_distrib := sorry

end Distrib_Class

class Semiring_Class (X : C) extends ComonObj X, AddMon_Class X, IsAddCommMon X, MonObj X,
    Distrib_Class X where
  zero_mul : zero ▷ X ≫ mul = (𝟙_ C) ◁ ε ≫ (λ_ _).hom ≫ zero
  mul_zero : X ◁ zero ≫ mul = ε ▷ (𝟙_ C) ≫ (ρ_ _).hom ≫ zero

namespace Semiring_Class

--@[simps!]
instance : Semiring_Class (𝟙_ C) where
  zero_mul := by sorry
  mul_zero := by sorry

end Semiring_Class

section IsSemiring_Hom

open scoped Semiring_Class

variable {M N O : C} [Semiring_Class M] [Semiring_Class N] [Semiring_Class O]

/-- The property that a morphism between monoid objects is a monoid morphism. -/
class IsSemiring_Hom (f : M ⟶ N) extends IsComonHom f, IsAddMon_Hom f, IsMonHom f

instance : IsSemiring_Hom (𝟙 M) where

instance (f : M ⟶ N) (g : N ⟶ O) [IsSemiring_Hom f] [IsSemiring_Hom g] : IsSemiring_Hom (f ≫ g) where

instance (f : M ≅ N) [IsSemiring_Hom f.hom] : IsSemiring_Hom f.inv where

end IsSemiring_Hom

variable (C) in
/-- A semiring object internal to a monoidal category.
-/
structure Semiring_ where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [semiring : Semiring_Class X]

attribute [instance] Semiring_.semiring

namespace Semiring_

variable (C) in
/-- The trivial monoid object. We later show this is initial in `AddMon_ C`.
-/
--@[simps!]
def trivial : Semiring_ C := mk (𝟙_ C)

instance : Inhabited (Semiring_ C) :=
  ⟨trivial C⟩

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : Semiring_ C) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [is_semiring_Hom : IsSemiring_Hom hom]

attribute [instance] Hom.is_semiring_Hom

/-- The identity morphism on a monoid object. -/
@[simps]
def id (M : Semiring_ C) : Hom M M := ⟨𝟙 M.X⟩

instance homInhabited (M : Semiring_ C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Semiring_ C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom
  is_semiring_Hom := instIsSemiring_HomComp f.hom g.hom

instance : Category (Semiring_ C) where
  Hom M N := Hom M N
  id := id
  comp := comp

end Semiring_

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
def addCommMon : AddCommMon_ C := AddCommMon_.fromCommMon_ (commMon α)

instance addMonClass : AddMon_Class α.A.A := (addCommMon α).toAddMon_ |>.mon

instance : IsAddCommMon α.A.A := addCommMon α |>.comm

/-- The internal semiring object associated to an algebra of the lifted bag monad to the category
of algebras of the list monad. -/
def toSemiring [SemiCartesianMonoidalCategory C] : Semiring_ C where
  X := α.A.A
  semiring :=
    { --toComon_Class := sorry
      toDistrib_Class := sorry
      zero_mul := by
        sorry
      mul_zero := by
        sorry
      counit := sorry
      comul := sorry

         }

/-- The equivalence of category of algebras of the lifted bag monad and the category of semiring objects. -/
def liftListBagAlgebraSemiringEquivalence [SemiCartesianMonoidalCategory C] :
    (Lift.monad (list.monad C) (bag.monad C)).Algebra ≌ Semiring_ C where
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
