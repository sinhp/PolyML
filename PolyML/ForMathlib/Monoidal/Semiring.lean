/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import PolyML.ForMathlib.Monad.Distrib
import PolyML.ForMathlib.Monoidal.AddMon_
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Distributive.Monoidal


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory Comon_Class Monad

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]

class Distrib_Class (X : C) [Comon_Class X] extends Mon_Class X, AddMon_Class X where
  left_distrib : Δ ▷ (X ⊗ X) ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ add = X ◁ add ≫ mul
  right_distrib : (X ⊗ X) ◁ Δ ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ add = add ▷ X ≫ mul

class LeftDistrib_Class (X : C) [Comon_Class X] extends Mon_Class X, AddMon_Class X where
  left_distrib : Δ ▷ (X ⊗ X) ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ add = X ◁ add ≫ mul

class RightDistrib_Class (X : C) [Comon_Class X] extends Mon_Class X, AddMon_Class X where
  right_distrib : (X ⊗ X) ◁ Δ ≫ tensorμ .. ≫ (mul ⊗ₘ mul) ≫ add = add ▷ X ≫ mul

alias mul_add := left_distrib

alias add_mul := right_distrib

instance (priority := 100) Distrib_Class.leftDistribClass (X : C) [Comon_Class X] [Distrib_Class X] :
    LeftDistrib_Class X :=
  ⟨Distrib_Class.left_distrib⟩

instance (priority := 100) Distrib_Class.rightDistribClass (X : C) [Comon_Class X] [Distrib_Class X] :
    RightDistrib_Class X :=
  ⟨Distrib_Class.right_distrib⟩

namespace Distrib_Class

instance : Distrib_Class (𝟙_ C) where
  left_distrib := sorry
  right_distrib := sorry

end Distrib_Class

class Semiring_Class (X : C) extends Comon_Class X, AddMon_Class X, IsAddCommMon X, Mon_Class X,
    Distrib_Class X where
  zero_mul : zero ▷ X ≫ mul = (𝟙_ C) ◁ ε ≫ (λ_ _).hom ≫ zero
  mul_zero : X ◁ zero ≫ mul = ε ▷ (𝟙_ C) ≫ (ρ_ _).hom ≫ zero

namespace Semiring_Class

@[simps]
instance : Semiring_Class (𝟙_ C) where
  zero_mul := by sorry
  mul_zero := by sorry

end Semiring_Class

open scoped Semiring_Class

variable {M N O : C} [Semiring_Class M] [Semiring_Class N] [Semiring_Class O]

/-- The property that a morphism between monoid objects is a monoid morphism. -/
class IsSemiring_Hom (f : M ⟶ N) extends IsComon_Hom f, IsAddMon_Hom f, IsMon_Hom f

instance : IsSemiring_Hom (𝟙 M) where

instance (f : M ⟶ N) (g : N ⟶ O) [IsSemiring_Hom f] [IsSemiring_Hom g] : IsSemiring_Hom (f ≫ g) where

instance {M N : C} [Semiring_Class M] [Semiring_Class N] (f : M ≅ N) [IsSemiring_Hom f.hom] :
   IsSemiring_Hom f.inv where

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
@[simps!]
def trivial : Semiring_ C := mk (𝟙_ C)

instance : Inhabited (Semiring_ C) :=
  ⟨trivial C⟩

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : Semiring_ C) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [isSemiring_Hom : IsSemiring_Hom hom]

instance : Category (Semiring_ C) where
  Hom M N := Hom M N
  id := sorry
  comp f g := sorry


end Semiring_

def liftingMonadAlgebraEquivalenceSemiring [ListArithmetic C] [WithBags C] :
    (LiftingMonad.monad (list.monad C) (bag.monad C)).Algebra ≌ Semiring_ C where
  functor := sorry
  inverse := sorry
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

end CategoryTheory


-- def Semiring_ :=
-- #check AddCommMonoid
-- #check IsCommMon



-- #check Mon_Class



-- open Distrib Monad



-- namespace Semiring_

-- variable {C} (α : Semiring_ C)

-- def X : C := α.A.A

-- instance mon_Class : Mon_Class α.X where
--   one := by
--     dsimp [X]
--     dsimp [Semiring_] at α
--     sorry
--   mul := by
--     dsimp [X];
--     sorry
--   one_mul := sorry
--   mul_one := sorry
--   mul_assoc := sorry

-- def mon : Mon_ C where
--   X := α.X

-- attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

-- instance commMon : CommMon_ C where
--   X := α.X
--   mon := sorry
--   comm := sorry
