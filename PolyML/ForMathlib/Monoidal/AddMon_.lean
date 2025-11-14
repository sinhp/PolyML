/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Group.PUnit
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# The category of monoids in a monoidal category.

We define monoids in a monoidal category `C` and show that the category of monoids is equivalent to
the category of lax monoidal functors from the unit monoidal category to `C`.  We also show that if
`C` is braided, then the category of monoids is naturally monoidal.

## Simp set for monoid object tautologies

In this file, we also provide a simp set called `mon_tauto` whose goal is to prove all tautologies
about morphisms from some (tensor) power of `M` to `M`, where `M` is a (commutative) monoid object
in a (braided) monoidal category.

Please read the documentation in `Mathlib/Tactic/Attr/Register.lean` for full details.

## TODO

* Implement to_additive for this. The whole file should be reduced to zero line.
-/

universe w v₁ v₂ v₃ u₁ u₂ u₃ u

open Function CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
class AddMonObj (X : C) where
  /-- The unit morphism of a monoid object. -/
  zero : 𝟙_ C ⟶ X
  /-- The multiplication morphism of a monoid object. -/
  add : X ⊗ X ⟶ X
  zero_add (X) : zero ▷ X ≫ add = (λ_ X).hom := by cat_disch
  add_zero (X) : X ◁ zero ≫ add = (ρ_ X).hom := by cat_disch
  -- Obviously there is some flexibility stating this axiom.
  -- This zero has left- and right-hand sides matching the statement of `Monoid.add_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  add_assoc (X) : (add ▷ X) ≫ add = (α_ X X X).hom ≫ (X ◁ add) ≫ add := by cat_disch

namespace AddMonObj
variable {A X Y : C} [AddMonObj A]

@[inherit_doc] scoped notation "μ" => AddMonObj.add
@[inherit_doc] scoped notation "μ["M"]" => AddMonObj.add (X := M)
@[inherit_doc] scoped notation "η" => AddMonObj.zero
@[inherit_doc] scoped notation "η["M"]" => AddMonObj.zero (X := M)

attribute [reassoc (attr := simp)] zero_add add_zero add_assoc

/-- Transfers an instance of `MonObj` to `AddMonObj` so that we can define `toSemiring`. -/
def fromMonObj {X : C} [MonObj X] : AddMonObj X where
  zero := MonObj.one
  add := MonObj.mul
  zero_add := MonObj.one_mul X
  add_zero := MonObj.mul_one X
  add_assoc := MonObj.mul_assoc X

/-- Transfer `AddMonObj` along an isomorphism. -/
-- Note: The simps lemmas are not tagged simp because their `#discr_tree_simp_key` are too generic.
@[simps! -isSimp]
def ofIso (e : A ≅ X) : AddMonObj X where
  zero := η[A] ≫ e.hom
  add := (e.inv ⊗ₘ e.inv) ≫ μ[A] ≫ e.hom
  zero_add := by
    rw [← cancel_epi (λ_ X).inv]
    simp only [comp_whiskerRight, tensorHom_def, Category.assoc,
      hom_inv_whiskerRight_assoc]
    simp [← tensorHom_def_assoc, leftUnitor_inv_comp_tensorHom_assoc]
  add_zero := by
    rw [← cancel_epi (ρ_ X).inv]
    simp only [MonoidalCategory.whiskerLeft_comp, tensorHom_def', Category.assoc,
      whiskerLeft_hom_inv_assoc, Iso.inv_hom_id]
    simp [← tensorHom_def'_assoc, rightUnitor_inv_comp_tensorHom_assoc]
  add_assoc := by simpa [← id_tensorHom, ← tensorHom_id,
      -associator_conjugation, associator_naturality_assoc] using
      congr(((e.inv ⊗ₘ e.inv) ⊗ₘ e.inv) ≫ $(AddMonObj.add_assoc A) ≫ e.hom)

@[simps]
instance : AddMonObj (𝟙_ C) where
  zero := 𝟙 _
  add := (λ_ _).hom
  add_assoc := by monoidal_coherence
  add_zero := by monoidal_coherence

@[ext]
theorem ext {X : C} (h₁ h₂ : AddMonObj X) (H : h₁.add = h₂.add) : h₁ = h₂ := by
  suffices h₁.zero = h₂.zero by cases h₁; cases h₂; subst H this; rfl
  trans (λ_ _).inv ≫ (h₁.zero ⊗ₘ h₂.zero) ≫ h₁.add
  · simp [tensorHom_def, H, ← unitors_equal]
  · simp [tensorHom_def']

end AddMonObj

open scoped AddMonObj

namespace Mathlib.Tactic.AddMonTauto
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {A W X X₁ X₂ X₃ Y Y₁ Y₂ Y₃ Z Z₁ Z₂ : C} [AddMonObj A]

attribute [mon_tauto] Category.id_comp Category.comp_id Category.assoc
  id_tensorHom_id tensorμ tensorδ
  tensorHom_comp_tensorHom tensorHom_comp_tensorHom_assoc
  leftUnitor_tensor_hom leftUnitor_tensor_hom_assoc
  leftUnitor_tensor_inv leftUnitor_tensor_inv_assoc
  rightUnitor_tensor_hom rightUnitor_tensor_hom_assoc
  rightUnitor_tensor_inv rightUnitor_tensor_inv_assoc

attribute [mon_tauto ←] tensorHom_id id_tensorHom

@[reassoc (attr := mon_tauto)]
lemma associator_hom_comp_tensorHom_tensorHom (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂) :
    (α_ X₁ Y₁ Z₁).hom ≫ (f ⊗ₘ g ⊗ₘ h) = ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ X₂ Y₂ Z₂).hom := by simp

@[reassoc (attr := mon_tauto)]
lemma associator_inv_comp_tensorHom_tensorHom (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂) :
    (α_ X₁ Y₁ Z₁).inv ≫ ((f ⊗ₘ g) ⊗ₘ h) = (f ⊗ₘ g ⊗ₘ h) ≫ (α_ X₂ Y₂ Z₂).inv := by simp

@[reassoc (attr := mon_tauto)]
lemma associator_hom_comp_tensorHom_tensorHom_comp (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
    (gh : Y₂ ⊗ Z₂ ⟶ W) :
    (α_ X₁ Y₁ Z₁).hom ≫ (f ⊗ₘ ((g ⊗ₘ h) ≫ gh)) =
      ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ X₂ Y₂ Z₂).hom ≫ (𝟙 _ ⊗ₘ gh) := by simp [tensorHom_def]

@[reassoc (attr := mon_tauto)]
lemma associator_inv_comp_tensorHom_tensorHom_comp (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
    (fg : X₂ ⊗ Y₂ ⟶ W) :
    (α_ X₁ Y₁ Z₁).inv ≫ (((f ⊗ₘ g) ≫ fg) ⊗ₘ h) =
      (f ⊗ₘ g ⊗ₘ h) ≫ (α_ X₂ Y₂ Z₂).inv ≫ (fg ⊗ₘ 𝟙 _) := by simp [tensorHom_def']

@[mon_tauto] lemma eq_one_mul : (λ_ A).hom = (η ⊗ₘ 𝟙 A) ≫ μ := by simp
@[mon_tauto] lemma eq_mul_one : (ρ_ A).hom = (𝟙 A ⊗ₘ η) ≫ μ := by simp

@[reassoc (attr := mon_tauto)] lemma leftUnitor_inv_one_tensor_mul (f : X₁ ⟶ A) :
    (λ_ _).inv ≫ (η ⊗ₘ f) ≫ μ = f := by simp [tensorHom_def']

@[reassoc (attr := mon_tauto)] lemma rightUnitor_inv_tensor_one_mul (f : X₁ ⟶ A) :
    (ρ_ _).inv ≫ (f ⊗ₘ η) ≫ μ = f := by simp [tensorHom_def]

@[reassoc (attr := mon_tauto)]
lemma mul_assoc_hom (f : X ⟶ A) :
    (α_ X A A).hom ≫ (f ⊗ₘ μ) ≫ μ = ((f ⊗ₘ 𝟙 A) ≫ μ ⊗ₘ 𝟙 A) ≫ μ := by simp [tensorHom_def]

@[reassoc (attr := mon_tauto)]
lemma mul_assoc_inv (f : X ⟶ A) :
    (α_ A A X).inv ≫ (μ ⊗ₘ f) ≫ μ = (𝟙 A ⊗ₘ (𝟙 A ⊗ₘ f) ≫ μ) ≫ μ  := by simp [tensorHom_def']

end Mathlib.Tactic.AddMonTauto

section

variable {M N O X : C} [AddMonObj M] [AddMonObj N] [AddMonObj O]

/-- The property that a morphism between monoid objects is a monoid morphism. -/
class IsAddMonHom (f : M ⟶ N) : Prop where
  zero_hom (f) : η ≫ f = η := by cat_disch
  add_hom (f) : μ ≫ f = (f ⊗ₘ f) ≫ μ := by cat_disch


attribute [reassoc (attr := simp)] IsAddMonHom.zero_hom IsAddMonHom.add_hom

instance : IsAddMonHom (𝟙 M) where

instance (f : M ⟶ N) (g : N ⟶ O) [IsAddMonHom f] [IsAddMonHom g] : IsAddMonHom (f ≫ g) where

attribute [local simp] AddMonObj.ofIso_zero AddMonObj.ofIso_add in
instance isAddMonHom_ofIso (e : M ≅ X) : letI := AddMonObj.ofIso e; IsAddMonHom e.hom := by
  letI := AddMonObj.ofIso e; exact { }

instance (f : M ≅ N) [IsAddMonHom f.hom] : IsAddMonHom f.inv where
  zero_hom := by simp [Iso.comp_inv_eq]
  add_hom := by simp [Iso.comp_inv_eq]

instance {f : M ⟶ N} [IsIso f] [IsAddMonHom f] : IsAddMonHom (asIso f).hom := ‹_›

end

variable (C) in
/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
structure AddMon where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [mon : AddMonObj X]

attribute [instance] AddMon.mon

namespace AddMon

variable (C) in
/-- The trivial monoid object. We later show this is initial in `Mon C`.
-/
@[simps!]
def trivial : AddMon C := mk (𝟙_ C)

instance : Inhabited (AddMon C) :=
  ⟨trivial C⟩

end AddMon

namespace AddMonObj

variable {M : C} [AddMonObj M]

@[simp]
theorem one_mul_hom {Z : C} (f : Z ⟶ M) : (η[M] ⊗ₘ f) ≫ μ[M] = (λ_ Z).hom ≫ f := by
  rw [tensorHom_def'_assoc, zero_add, leftUnitor_naturality]

@[simp]
theorem mul_zero_hom {Z : C} (f : Z ⟶ M) : (f ⊗ₘ η[M]) ≫ μ[M] = (ρ_ Z).hom ≫ f := by
  rw [tensorHom_def_assoc, add_zero, rightUnitor_naturality]

variable (M) in
@[reassoc]
theorem mul_assoc_flip : M ◁ μ ≫ μ = (α_ M M M).inv ≫ μ ▷ M ≫ μ := by
  simp

end AddMonObj

namespace AddMonObj

/-!
In this section, we prove that the category of monoids in a braided monoidal category is monoidal.

Given two monoids `M` and `N` in a braided monoidal category `C`,
the multiplication on the tensor product `M.X ⊗ N.X` is defined in the obvious way:
it is the tensor product of the multiplications on `M` and `N`,
except that the tensor factors in the source come in the wrong order,
which we fix by pre-composing with a permutation isomorphism constructed from the braiding.

(There is a subtlety here: in fact there are two ways to do these,
using either the positive or negative crossing.)

A more conceptual way of understanding this definition is the following:
The braiding on `C` gives rise to a monoidal structure on
the tensor product functor from `C × C` to `C`.
A pair of monoids in `C` gives rise to a monoid in `C × C`,
which the tensor product functor by being monoidal takes to a monoid in `C`.
The permutation isomorphism appearing in the definition of
the multiplication on the tensor product of two monoids is
an instance of a more general family of isomorphisms
which together form a strength that equips the tensor product functor with a monoidal structure,
and the monoid axioms for the tensor product follow from the monoid axioms for the tensor factors
plus the properties of the strength (i.e., monoidal functor axioms).
The strength `tensorμ` of the tensor product functor has been defined in
`Mathlib/CategoryTheory/Monoidal/Braided.lean`.
Its properties, stated as independent lemmas in that module,
are used extensively in the proofs below.
Notice that we could have followed the above plan not only conceptually
but also as a possible implementation and
could have constructed the tensor product of monoids via `mapAddMon`,
but we chose to give a more explicit definition directly in terms of `tensorμ`.

To complete the definition of the monoidal category structure on the category of monoids,
we need to provide definitions of associator and unitors.
The obvious candidates are the associator and unitors from `C`,
but we need to prove that they are monoid morphisms, i.e., compatible with unit and multiplication.
These properties translate to the monoidality of the associator and unitors
(with respect to the monoidal structures on the functors they relate),
which have also been proved in `Mathlib/CategoryTheory/Monoidal/Braided.lean`.

-/

-- The proofs that associators and unitors preserve monoid units don't require braiding.
lemma one_associator {M N P : C} [AddMonObj M] [AddMonObj N] [AddMonObj P] :
    ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ η[N]) ⊗ₘ η[P])) ≫ (α_ M N P).hom =
      (λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ (λ_ (𝟙_ C)).inv ≫ (η[N] ⊗ₘ η[P])) := by
  simp only [Category.assoc, Iso.cancel_iso_inv_left]
  slice_lhs 1 3 => rw [← Category.id_comp (η : 𝟙_ C ⟶ P), ← tensorHom_comp_tensorHom]
  slice_lhs 2 3 => rw [associator_naturality]
  slice_rhs 1 2 => rw [← Category.id_comp η, ← tensorHom_comp_tensorHom]
  slice_lhs 1 2 => rw [tensorHom_id, ← leftUnitor_tensor_inv]
  rw [← cancel_epi (λ_ (𝟙_ C)).inv]
  slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
  simp

lemma one_leftUnitor {M : C} [AddMonObj M] :
    ((λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ η[M])) ≫ (λ_ M).hom = η := by
  simp

lemma one_rightUnitor {M : C} [AddMonObj M] :
    ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ 𝟙 (𝟙_ C))) ≫ (ρ_ M).hom = η := by
  simp [← unitors_equal]

section BraidedCategory

variable [BraidedCategory C]

lemma Mon_tensor_one_mul (M N : C) [AddMonObj M] [AddMonObj N] :
    (((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ η[N])) ▷ (M ⊗ N)) ≫
        tensorμ M N M N ≫ (μ ⊗ₘ μ) =
      (λ_ (M ⊗ N)).hom := by
  simp only [comp_whiskerRight_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, zero_add, zero_add]
  symm
  exact tensor_left_unitality M N

lemma Mon_tensor_mul_one (M N : C) [AddMonObj M] [AddMonObj N] :
    (M ⊗ N) ◁ ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ η[N])) ≫
        tensorμ M N M N ≫ (μ[M] ⊗ₘ μ[N]) =
      (ρ_ (M ⊗ N)).hom := by
  simp only [whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_right]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, add_zero, add_zero]
  symm
  exact tensor_right_unitality M N

lemma Mon_tensor_mul_assoc (M N : C) [AddMonObj M] [AddMonObj N] :
    ((tensorμ M N M N ≫ (μ ⊗ₘ μ)) ▷ (M ⊗ N)) ≫
        tensorμ M N M N ≫ (μ ⊗ₘ μ) =
      (α_ (M ⊗ N : C) (M ⊗ N) (M ⊗ N)).hom ≫
        ((M ⊗ N : C) ◁ (tensorμ M N M N ≫ (μ ⊗ₘ μ))) ≫
          tensorμ M N M N ≫ (μ ⊗ₘ μ) := by
  simp only [comp_whiskerRight_assoc, whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, add_assoc, add_assoc, ← tensorHom_comp_tensorHom,
    ← tensorHom_comp_tensorHom]
  slice_lhs 1 3 => rw [tensor_associativity]
  slice_lhs 3 4 => rw [← tensorμ_natural_right]
  simp

lemma mul_associator {M N P : C} [AddMonObj M] [AddMonObj N] [AddMonObj P] :
    (tensorμ (M ⊗ N) P (M ⊗ N) P ≫
          (tensorμ M N M N ≫ (μ ⊗ₘ μ) ⊗ₘ μ)) ≫
        (α_ M N P).hom =
      ((α_ M N P).hom ⊗ₘ (α_ M N P).hom) ≫
        tensorμ M (N ⊗ P) M (N ⊗ P) ≫
          (μ ⊗ₘ tensorμ N P N P ≫ (μ ⊗ₘ μ)) := by
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← Category.id_comp μ[P], ← tensorHom_comp_tensorHom]
  slice_lhs 3 4 => rw [associator_naturality]
  slice_rhs 3 4 => rw [← Category.id_comp μ, ← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 1 3 => rw [associator_monoidal]
  simp only [Category.assoc]

lemma mul_leftUnitor {M : C} [AddMonObj M] :
    (tensorμ (𝟙_ C) M (𝟙_ C) M ≫ ((λ_ (𝟙_ C)).hom ⊗ₘ μ)) ≫ (λ_ M).hom =
      ((λ_ M).hom ⊗ₘ (λ_ M).hom) ≫ μ := by
  rw [← Category.comp_id (λ_ (𝟙_ C)).hom, ← Category.id_comp μ, ← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 1 3 => rw [← leftUnitor_monoidal]
  simp only [Category.id_comp]

lemma mul_rightUnitor {M : C} [AddMonObj M] :
    (tensorμ M (𝟙_ C) M (𝟙_ C) ≫ (μ ⊗ₘ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ M).hom =
      ((ρ_ M).hom ⊗ₘ (ρ_ M).hom) ≫ μ := by
  rw [← Category.id_comp μ, ← Category.comp_id (λ_ (𝟙_ C)).hom, ← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  slice_lhs 1 3 => rw [← rightUnitor_monoidal]
  simp only [Category.id_comp]

namespace tensorObj

-- We don't want `tensorObj.zero_def` to be simp as it would loop with `IsAddMonHom.zero_hom` applied
-- to `(λ_ N.X).inv`.
@[simps -isSimp]
instance {M N : C} [AddMonObj M] [AddMonObj N] : AddMonObj (M ⊗ N) where
  zero := (λ_ (𝟙_ C)).inv ≫ (η ⊗ₘ η)
  add := tensorμ M N M N ≫ (μ ⊗ₘ μ)
  zero_add := Mon_tensor_one_mul M N
  add_zero := Mon_tensor_mul_one M N
  add_assoc := Mon_tensor_mul_assoc M N

end tensorObj

open IsAddMonHom

variable {X Y Z W : C} [AddMonObj X] [AddMonObj Y] [AddMonObj Z] [AddMonObj W]

instance {f : X ⟶ Y} {g : Z ⟶ W} [IsAddMonHom f] [IsAddMonHom g] : IsAddMonHom (f ⊗ₘ g) where
  zero_hom := by
    dsimp [tensorObj.zero_def]
    slice_lhs 2 3 => rw [tensorHom_comp_tensorHom, zero_hom, zero_hom]
  add_hom := by
    dsimp [tensorObj.add_def]
    slice_rhs 1 2 => rw [tensorμ_natural]
    slice_lhs 2 3 => rw [tensorHom_comp_tensorHom, add_hom, add_hom, ← tensorHom_comp_tensorHom]
    simp only [Category.assoc]

instance : IsAddMonHom (𝟙 X) where

instance {f : Y ⟶ Z} [IsAddMonHom f] : IsAddMonHom (X ◁ f) where
  zero_hom := by simpa using (inferInstanceAs <| IsAddMonHom (𝟙 X ⊗ₘ f)).zero_hom
  add_hom := by simpa using (inferInstanceAs <| IsAddMonHom (𝟙 X ⊗ₘ f)).add_hom

instance {f : X ⟶ Y} [IsAddMonHom f] : IsAddMonHom (f ▷ Z) where
  zero_hom := by simpa using (inferInstanceAs <| IsAddMonHom (f ⊗ₘ (𝟙 Z))).zero_hom
  add_hom := by simpa using (inferInstanceAs <| IsAddMonHom (f ⊗ₘ (𝟙 Z))).add_hom

instance : IsAddMonHom (α_ X Y Z).hom :=
  ⟨one_associator, mul_associator⟩

instance : IsAddMonHom (λ_ X).hom :=
  ⟨one_leftUnitor, mul_leftUnitor⟩

instance : IsAddMonHom (ρ_ X).hom :=
  ⟨one_rightUnitor, mul_rightUnitor⟩

lemma one_braiding (X Y : C) [AddMonObj X] [AddMonObj Y] : η ≫ (β_ X Y).hom = η := by
  simp only [tensorObj.zero_def, Category.assoc, BraidedCategory.braiding_naturality,
    braiding_tensorUnit_right, Iso.cancel_iso_inv_left]
  monoidal

end BraidedCategory

end AddMonObj

namespace AddMon

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : AddMon C) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [isMonHom_hom : IsAddMonHom hom]

attribute [instance] Hom.isMonHom_hom

/-- Construct a morphism `M ⟶ N` of `Mon C` from a map `f : M ⟶ N` and a `IsAddMonHom f` instance. -/
abbrev Hom.mk' {M N : AddMon C} (f : M.X ⟶ N.X)
    (one_f : η ≫ f = η := by cat_disch)
    (mul_f : μ ≫ f = (f ⊗ₘ f) ≫ μ := by cat_disch) : Hom M N :=
  have : IsAddMonHom f := ⟨one_f, mul_f⟩
  .mk f

/-- The identity morphism on a monoid object. -/
@[simps]
def id (M : AddMon C) : Hom M M := ⟨𝟙 M.X⟩

instance homInhabited (M : AddMon C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : AddMon C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

instance : Category (AddMon C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

instance {M N : AddMon C} (f : M ⟶ N) : IsAddMonHom f.hom := f.isMonHom_hom

@[ext]
lemma Hom.ext' {M N : AddMon C} {f g : M ⟶ N} (w : f.hom = g.hom) : f = g :=
  Hom.ext w

lemma hom_injective {M N : AddMon C} : Injective (Hom.hom : (M ⟶ N) → (M.X ⟶ N.X)) :=
  fun _ _ ↦ Hom.ext

@[simp]
theorem id_hom' (M : AddMon C) : (𝟙 M : Hom M M).hom = 𝟙 M.X :=
  rfl

@[simp]
theorem comp_hom' {M N K : AddMon C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl

section

variable (C)

/-- The forgetful functor from monoid objects to the ambient category. -/
@[simps]
def forget : AddMon C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : (forget C).Faithful where

instance {A B : AddMon C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom :=
  e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e := ⟨⟨.mk' (inv f.hom), by cat_disch⟩⟩

instance {M N : AddMon C} {f : M ⟶ N} [IsIso f] : IsIso f.hom :=
  inferInstanceAs <| IsIso <| (forget C).map f

/-- Construct an isomorphism of monoid objects by giving a monoid isomorphism between the underlying
objects. -/
@[simps]
def mkIso' {M N : C} [AddMonObj M] [AddMonObj N] (e : M ≅ N) [IsAddMonHom e.hom] : mk M ≅ mk N where
  hom := Hom.mk e.hom
  inv := Hom.mk e.inv

/-- Construct an isomorphism of monoid objects by giving an isomorphism between the underlying
objects and checking compatibility with unit and multiplication only in the forward direction. -/
@[simps!]
abbrev mkIso {M N : AddMon C} (e : M.X ≅ N.X) (one_f : η[M.X] ≫ e.hom = η[N.X] := by cat_disch)
    (mul_f : μ[M.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[N.X] := by cat_disch) : M ≅ N :=
  have : IsAddMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

@[simps]
instance uniqueHomFromTrivial (A : AddMon C) : Unique (trivial C ⟶ A) where
  default.hom := η[A.X]
  default.isMonHom_hom.add_hom := by simp [unitors_equal]
  uniq f := by
    ext
    rw [← Category.id_comp f.hom]
    dsimp only [trivial_X]
    rw [← trivial_mon_zero, IsAddMonHom.zero_hom]

open CategoryTheory.Limits

instance : HasInitial (AddMon C) :=
  hasInitial_of_unique (AddMon.trivial C)

section BraidedCategory
variable [BraidedCategory C]

@[simps! tensorObj_X tensorHom_hom]
instance monMonoidalStruct : MonoidalCategoryStruct (AddMon C) where
  tensorObj M N := ⟨M.X ⊗ N.X⟩
  tensorHom f g := Hom.mk (f.hom ⊗ₘ g.hom)
  whiskerRight f Y := Hom.mk (f.hom ▷ Y.X)
  whiskerLeft X _ _ g := Hom.mk (X.X ◁ g.hom)
  tensorUnit := ⟨𝟙_ C⟩
  associator M N P := mkIso' <| associator M.X N.X P.X
  leftUnitor M := mkIso' <| leftUnitor M.X
  rightUnitor M := mkIso' <| rightUnitor M.X

@[simp] lemma tensorUnit_X : (𝟙_ (AddMon C)).X = 𝟙_ C := rfl
@[simp] lemma tensorUnit_one : η[(𝟙_ (AddMon C)).X] = 𝟙 (𝟙_ C) := rfl
@[simp] lemma tensorUnit_mul : μ[(𝟙_ (AddMon C)).X] = (λ_ (𝟙_ C)).hom := rfl

@[simp]
lemma tensorObj_one (X Y : AddMon C) : η[(X ⊗ Y).X] = (λ_ (𝟙_ C)).inv ≫ (η[X.X] ⊗ₘ η[Y.X]) := rfl

@[simp] lemma tensorObj_mul (X Y : AddMon C) :
    μ[(X ⊗ Y).X] = tensorμ X.X Y.X X.X Y.X ≫ (μ[X.X] ⊗ₘ μ[Y.X]) := rfl

@[simp]
lemma whiskerLeft_hom {X Y : AddMon C} (f : X ⟶ Y) (Z : AddMon C) : (f ▷ Z).hom = f.hom ▷ Z.X := rfl

@[simp]
lemma whiskerRight_hom (X : AddMon C) {Y Z : AddMon C} (f : Y ⟶ Z) : (X ◁ f).hom = X.X ◁ f.hom := rfl

@[simp] lemma leftUnitor_hom_hom (X : AddMon C) : (λ_ X).hom.hom = (λ_ X.X).hom := rfl
@[simp] lemma leftUnitor_inv_hom (X : AddMon C) : (λ_ X).inv.hom = (λ_ X.X).inv := rfl
@[simp] lemma rightUnitor_hom_hom (X : AddMon C) : (ρ_ X).hom.hom = (ρ_ X.X).hom := rfl
@[simp] lemma rightUnitor_inv_hom (X : AddMon C) : (ρ_ X).inv.hom = (ρ_ X.X).inv := rfl

@[simp] lemma associator_hom_hom (X Y Z : AddMon C) : (α_ X Y Z).hom.hom = (α_ X.X Y.X Z.X).hom := rfl
@[simp] lemma associator_inv_hom (X Y Z : AddMon C) : (α_ X Y Z).inv.hom = (α_ X.X Y.X Z.X).inv := rfl

@[simp] lemma tensor_one (M N : AddMon C) : η[(M ⊗ N).X] = (λ_ (𝟙_ C)).inv ≫ (η[M.X] ⊗ₘ η[N.X]) := rfl

@[simp]
lemma tensor_mul (M N : AddMon C) : μ[(M ⊗ N).X] = tensorμ M.X N.X M.X N.X ≫ (μ[M.X] ⊗ₘ μ[N.X]) := rfl

instance monMonoidal : MonoidalCategory (AddMon C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]

-- We don't want `tensorObj.zero_def` to be simp as it would loop with `IsAddMonHom.zero_hom` applied
-- to `(λ_ N.X).inv`.
@[simps! -isSimp]
instance {M N : C} [AddMonObj M] [AddMonObj N] : AddMonObj (M ⊗ N) :=
  inferInstanceAs <| AddMonObj (AddMon.mk M ⊗ AddMon.mk N).X

variable (C)

/-- The forgetful functor from `Mon C` to `C` is monoidal when `C` is monoidal. -/
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

@[simp] lemma forget_ε : ε (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] lemma forget_η : «η» (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] lemma forget_μ (X Y : AddMon C) : «μ» (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl
@[simp] lemma forget_δ (X Y : AddMon C) : δ (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl

end BraidedCategory
end AddMon

/-!
We next show that if `C` is symmetric, then `Mon C` is braided, and indeed symmetric.

Note that `Mon C` is *not* braided in general when `C` is only braided.

The more interesting construction is the 2-category of monoids in `C`,
bimodules between the monoids, and intertwiners between the bimodules.

When `C` is braided, that is a monoidal 2-category.
-/
section SymmetricCategory

variable [SymmetricCategory C]

namespace AddMonObj

lemma mul_braiding (X Y : C) [AddMonObj X] [AddMonObj Y] :
    μ ≫ (β_ X Y).hom = ((β_ X Y).hom ⊗ₘ (β_ X Y).hom) ≫ μ := by
  dsimp [tensorObj.add_def]
  simp only [tensorμ, Category.assoc, BraidedCategory.braiding_naturality,
    BraidedCategory.braiding_tensor_right_hom, BraidedCategory.braiding_tensor_left_hom,
    comp_whiskerRight, whisker_assoc, whiskerLeft_comp, pentagon_assoc,
    pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
  slice_lhs 3 4 =>
    -- We use symmetry here:
    rw [← whiskerLeft_comp, ← comp_whiskerRight, SymmetricCategory.symmetry]
  simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.assoc, pentagon_inv_assoc,
    Iso.hom_inv_id_assoc]
  slice_lhs 1 2 =>
    rw [← associator_inv_naturality_left]
  slice_lhs 2 3 =>
    rw [Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 2 3 =>
    rw [← associator_naturality_right]
  slice_lhs 1 2 =>
    rw [← tensorHom_def]
  simp only [Category.assoc]

instance {X Y : C} [AddMonObj X] [AddMonObj Y] : IsAddMonHom (β_ X Y).hom :=
  ⟨one_braiding X Y, mul_braiding X Y⟩

end AddMonObj

namespace AddMon

instance : SymmetricCategory (AddMon C) where
  braiding X Y := mkIso' (β_ X.X Y.X)

@[simp] lemma braiding_hom_hom (M N : AddMon C) : (β_ M N).hom.hom = (β_ M.X N.X).hom := rfl
@[simp] lemma braiding_inv_hom (M N : AddMon C) : (β_ M N).inv.hom = (β_ M.X N.X).inv := rfl

end AddMon
end SymmetricCategory

variable
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
  {F F' : C ⥤ D} {G : D ⥤ E}

namespace Functor

section LaxMonoidal
variable [F.LaxMonoidal] [F'.LaxMonoidal] [G.LaxMonoidal] (X Y : C) [AddMonObj X] [AddMonObj Y]
  (f : X ⟶ Y) [IsAddMonHom f]

/-- The image of a monoid object under a lax monoidal functor is a monoid object. -/
abbrev addMonObjObj : AddMonObj (F.obj X) where
  zero := ε F ≫ F.map η
  add := LaxMonoidal.μ F X X ≫ F.map μ
  zero_add := by simp [← F.map_comp]
  add_zero := by simp [← F.map_comp]
  add_assoc := by
    simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, AddMonObj.add_assoc]
    simp

scoped[CategoryTheory.Obj] attribute [instance] CategoryTheory.Functor.addMonObjObj

open scoped Obj

@[reassoc, simp] lemma AddMon.obj.η_def : (η : 𝟙_ D ⟶ F.obj X) = ε F ≫ F.map η := rfl

@[reassoc, simp] lemma AddMon.obj.μ_def : μ = LaxMonoidal.μ F X X ≫ F.map μ := rfl

instance map.instIsAddMonHom : IsAddMonHom (F.map f) where
  zero_hom := by simp [← map_comp]
  add_hom := by simp [← map_comp]


open AddMonObj

-- TODO: mapMod F A : Mod A ⥤ Mod (F.mapAddMon A)
variable (F) in
/-- A lax monoidal functor takes monoid objects to monoid objects.

That is, a lax monoidal functor `F : C ⥤ D` induces a functor `Mon C ⥤ AddMon D`.
-/
@[simps]
def mapAddMon : AddMon C ⥤ AddMon D where
  obj A := .mk (F.obj A.X)
  map f := .mk (F.map f.hom)

@[simp]
theorem id_mapAddMon_one (X : AddMon C) : η[((𝟭 C).mapAddMon.obj X).X] = 𝟙 _ ≫ η[X.X] := rfl

@[simp]
theorem id_mapAddMon_mul (X : AddMon C) : μ[((𝟭 C).mapAddMon.obj X).X] = 𝟙 _ ≫ μ[X.X] := rfl

@[simp]
theorem comp_mapAddMon_one (X : AddMon C) :
    η[((F ⋙ G).mapAddMon.obj X).X] = ε (F ⋙ G) ≫ (F ⋙ G).map η[X.X] :=
  rfl

@[simp]
theorem comp_mapAddMon_mul (X : AddMon C) :
    μ[((F ⋙ G).mapAddMon.obj X).X] = «μ» (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[X.X] :=
  rfl

/-- The identity functor is also the identity on monoid objects. -/
@[simps!]
def mapAddMonIdIso : mapAddMon (𝟭 C) ≅ 𝟭 (AddMon C) :=
  NatIso.ofComponents fun X ↦ AddMon.mkIso (.refl _)

/-- The composition functor is also the composition on monoid objects. -/
@[simps!]
def mapAddMonCompIso : (F ⋙ G).mapAddMon ≅ F.mapAddMon ⋙ G.mapAddMon :=
  NatIso.ofComponents fun X ↦ AddMon.mkIso (.refl _)

protected instance Faithful.mapAddMon [F.Faithful] : F.mapAddMon.Faithful where
  map_injective {_X _Y} _f _g hfg := AddMon.Hom.ext <| map_injective congr(($hfg).hom)

/-- Natural transformations between functors lift to monoid objects. -/
@[simps!]
def mapAddMonNatTrans (f : F ⟶ F') [NatTrans.IsMonoidal f] : F.mapAddMon ⟶ F'.mapAddMon where
  app X := .mk' (f.app _)

/-- Natural isomorphisms between functors lift to monoid objects. -/
@[simps!]
def mapAddMonNatIso (e : F ≅ F') [NatTrans.IsMonoidal e.hom] : F.mapAddMon ≅ F'.mapAddMon :=
  NatIso.ofComponents fun X ↦ AddMon.mkIso (e.app _)

attribute [local simp] ε_tensorHom_comp_μ_assoc in
instance [F.LaxMonoidal] : IsAddMonHom (ε F) where

end LaxMonoidal


section OplaxMonoidal
variable [F.OplaxMonoidal]

open scoped AddMonObj in
/-- Pullback a monoid object along a fully faithful oplax monoidal functor. -/
@[simps]
abbrev FullyFaithful.AddMonObj (hF : F.FullyFaithful) (X : C) [AddMonObj (F.obj X)] : AddMonObj X where
  zero := hF.preimage <| OplaxMonoidal.η F ≫ η[F.obj X]
  add := hF.preimage <| OplaxMonoidal.δ F X X ≫ μ[F.obj X]
  zero_add := hF.map_injective <| by simp [← δ_natural_left_assoc]
  add_zero := hF.map_injective <| by simp [← δ_natural_right_assoc]
  add_assoc := hF.map_injective <| by simp [← δ_natural_left_assoc, ← δ_natural_right_assoc]

end OplaxMonoidal

section Monoidal
variable [F.Monoidal]

open scoped Obj
protected instance Full.mapAddMon [F.Full] [F.Faithful] : F.mapAddMon.Full where
  map_surjective {X Y} f :=
    let ⟨g, hg⟩ := F.map_surjective f.hom
    ⟨{
      hom := g
      isMonHom_hom.zero_hom :=
        F.map_injective <| by simpa [← hg, cancel_epi] using IsAddMonHom.zero_hom f.hom
      isMonHom_hom.add_hom :=
        F.map_injective <| by simpa [← hg, cancel_epi] using IsAddMonHom.add_hom f.hom },
      AddMon.Hom.ext hg⟩

instance isAddMonHom_preimage (hF : F.FullyFaithful) {X Y : C}
    [AddMonObj X] [AddMonObj Y] (f : F.obj X ⟶ F.obj Y) [IsAddMonHom f] :
    IsAddMonHom (hF.preimage f) where
  zero_hom := hF.map_injective <| by simp [← AddMon.obj.η_def_assoc, ← AddMon.obj.η_def, ← cancel_epi (ε F)]
  add_hom := hF.map_injective <| by
    simp [← AddMon.obj.μ_def_assoc, ← AddMon.obj.μ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)]

/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then `Mon(F) : AddMon C ⥤ AddMon D` is fully
faithful too. -/
@[simps]
protected def FullyFaithful.mapAddMon (hF : F.FullyFaithful) : F.mapAddMon.FullyFaithful where
  preimage {X Y} f := .mk' <| hF.preimage f.hom

attribute [local simp] AddMonObj.ofIso_zero AddMonObj.ofIso_add in
open Monoidal in
/-- The essential image of a fully faithful functor between cartesian-monoidal categories is the
same on monoid objects as on objects. -/
@[simp] lemma essImage_mapAddMon [F.Full] [F.Faithful] {M : AddMon D} :
    F.mapAddMon.essImage M ↔ F.essImage M.X where
  mp := by rintro ⟨N, ⟨e⟩⟩; exact ⟨N.X, ⟨(AddMon.forget _).mapIso e⟩⟩
  mpr := by
    rintro ⟨N, ⟨e⟩⟩
    let : AddMonObj (F.obj N) := .ofIso e.symm
    let : AddMonObj N := (FullyFaithful.ofFullyFaithful F).AddMonObj N
    refine ⟨.mk N, ⟨AddMon.mkIso e ?_ ?_⟩⟩ <;> simp

end Monoidal

section BraidedCategory
variable [BraidedCategory C] [BraidedCategory D] (F)

open scoped Obj

attribute [-simp] IsAddMonHom.zero_hom_assoc in
attribute [local simp← ] tensorHom_comp_tensorHom tensorHom_comp_tensorHom_assoc in
attribute [local simp] tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc AddMonObj.tensorObj.zero_def
  AddMonObj.tensorObj.add_def in
instance [F.LaxBraided] (M N : C) [AddMonObj M] [AddMonObj N] : IsAddMonHom («μ» F M N) where
  zero_hom := by simp [← Functor.map_comp, leftUnitor_inv_comp_tensorHom_assoc]

attribute [-simp] IsAddMonHom.zero_hom IsAddMonHom.zero_hom_assoc IsAddMonHom.add_hom in
attribute [local simp] ε_tensorHom_comp_μ_assoc tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc
  AddMonObj.tensorObj.zero_def AddMonObj.tensorObj.add_def in
instance [F.LaxBraided] : F.mapAddMon.LaxMonoidal where
  ε := .mk (ε F)
  «μ» M N := .mk («μ» F M.X N.X)

attribute [-simp] IsAddMonHom.zero_hom IsAddMonHom.zero_hom_assoc IsAddMonHom.add_hom in
attribute [local simp← ] tensorHom_comp_tensorHom tensorHom_comp_tensorHom_assoc in
attribute [local simp] ε_tensorHom_comp_μ_assoc tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc
  AddMonObj.tensorObj.zero_def AddMonObj.tensorObj.add_def in
instance [F.Braided] : F.mapAddMon.Monoidal :=
  CoreMonoidal.toMonoidal {
    εIso := AddMon.mkIso (Monoidal.εIso F)
    μIso M N := AddMon.mkIso (Monoidal.μIso F M.X N.X) <| by simp [← Functor.map_comp]
  }

end BraidedCategory

variable [SymmetricCategory C] [SymmetricCategory D]

instance [F.LaxBraided] : F.mapAddMon.LaxBraided where
  braided M N := by ext; exact Functor.LaxBraided.braided ..

instance [F.Braided] : F.mapAddMon.Braided where

variable (C D) in
/-- `mapAddMon` is functorial in the lax monoidal functor. -/
@[simps]
def mapAddMonFunctor : LaxMonoidalFunctor C D ⥤ AddMon C ⥤ AddMon D where
  obj F := F.mapAddMon
  map α := { app A := .mk' (α.hom.app A.X) }
  map_comp _ _ := rfl

end Functor

open Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [a.IsMonoidal]

/-- An adjunction of monoidal functors lifts to an adjunction of their lifts to monoid objects. -/
@[simps] def mapAddMon : F.mapAddMon ⊣ G.mapAddMon where
  unit := mapAddMonIdIso.inv ≫ mapAddMonNatTrans a.unit ≫ mapAddMonCompIso.hom
  counit := mapAddMonCompIso.inv ≫ mapAddMonNatTrans a.counit ≫ mapAddMonIdIso.hom

end Adjunction

namespace Equivalence

/-- An equivalence of categories lifts to an equivalence of their monoid objects. -/
@[simps]
def mapAddMon (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal] :
    AddMon C ≌ AddMon D where
  functor := e.functor.mapAddMon
  inverse := e.inverse.mapAddMon
  unitIso := mapAddMonIdIso.symm ≪≫ mapAddMonNatIso e.unitIso ≪≫ mapAddMonCompIso
  counitIso := mapAddMonCompIso.symm ≪≫ mapAddMonNatIso e.counitIso ≪≫ mapAddMonIdIso

end Equivalence

namespace AddMon

namespace EquivLaxMonoidalFunctorPUnit

variable (C) in
/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def laxMonoidalToMon : LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C ⥤ AddMon C where
  obj F := (F.mapAddMon : AddMon _ ⥤ AddMon C).obj (trivial (Discrete PUnit))
  map α := ((Functor.mapAddMonFunctor (Discrete PUnit) C).map α).app _

/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def monToLaxMonoidalObj (A : AddMon C) :
    Discrete PUnit.{w + 1} ⥤ C := (Functor.const _).obj A.X

instance (A : AddMon C) : (monToLaxMonoidalObj A).LaxMonoidal where
  ε := η[A.X]
  «μ» _ _ := μ[A.X]

@[simp]
lemma monToLaxMonoidalObj_ε (A : AddMon C) :
    ε (monToLaxMonoidalObj A) = η[A.X] := rfl

@[simp]
lemma monToLaxMonoidalObj_μ (A : AddMon C) (X Y) :
    «μ» (monToLaxMonoidalObj A) X Y = μ[A.X] := rfl

variable (C)
/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def monToLaxMonoidal : AddMon C ⥤ LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C where
  obj A := LaxMonoidalFunctor.of (monToLaxMonoidalObj A)
  map f :=
    { hom := { app _ := f.hom }
      isMonoidal := { } }

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def unitIso :
    𝟭 (LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C) ≅ laxMonoidalToMon C ⋙ monToLaxMonoidal C :=
  NatIso.ofComponents
    (fun F ↦ LaxMonoidalFunctor.isoOfComponents (fun _ ↦ F.mapIso (eqToIso (by ext))))

/-- Auxiliary definition for `counitIso`. -/
@[simps!]
def counitIsoAux (F : AddMon C) :
    ((monToLaxMonoidal.{w} C ⋙ laxMonoidalToMon C).obj F).X ≅ ((𝟭 (AddMon C)).obj F).X :=
  Iso.refl _

@[simp]
theorem monToLaxMonoidal_laxMonoidalToMon_obj_one (F : AddMon C) :
    η[((monToLaxMonoidal C ⋙ laxMonoidalToMon C).obj F).X] = η[F.X] ≫ 𝟙 _ :=
  rfl

@[simp]
theorem monToLaxMonoidal_laxMonoidalToMon_obj_mul (F : AddMon C) :
    μ[((monToLaxMonoidal C ⋙ laxMonoidalToMon C).obj F).X] = μ[F.X] ≫ 𝟙 _ :=
  rfl

theorem isMonHom_counitIsoAux (F : AddMon C) :
    IsAddMonHom (counitIsoAux C F).hom where

@[deprecated (since := "2025-09-15")] alias counitIsoAux_IsMon_Hom := isMonHom_counitIsoAux

/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def counitIso : monToLaxMonoidal.{w} C ⋙ laxMonoidalToMon C ≅ 𝟭 (AddMon C) :=
  NatIso.ofComponents fun F ↦
    letI : IsAddMonHom (counitIsoAux.{w} C F).hom := isMonHom_counitIsoAux C F
    mkIso (counitIsoAux.{w} C F)

end EquivLaxMonoidalFunctorPUnit

open EquivLaxMonoidalFunctorPUnit

attribute [local simp] eqToIso_map

/--
Monoid objects in `C` are "just" lax monoidal functors from the trivial monoidal category to `C`.
-/
@[simps]
def equivLaxMonoidalFunctorPUnit : LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C ≌ AddMon C where
  functor := laxMonoidalToMon C
  inverse := monToLaxMonoidal C
  unitIso := unitIso C
  counitIso := counitIso C

end AddMon

section

variable [BraidedCategory.{v₁} C]

/-- Predicate for a monoid object to be commutative. -/
class IsAddCommMonObj (X : C) [AddMonObj X] where
  add_comm (X) : (β_ X X).hom ≫ μ = μ := by cat_disch

open scoped AddMonObj

namespace IsAddCommMonObj

attribute [reassoc (attr := simp, mon_tauto)] add_comm

variable {M : C} [AddMonObj M]

variable (M) in
@[reassoc (attr := simp, mon_tauto)]
lemma add_comm' [IsAddCommMonObj M] : (β_ M M).inv ≫ μ = μ := by simp [← cancel_epi (β_ M M).hom]

instance : IsAddCommMonObj (𝟙_ C) where
  add_comm := by dsimp; rw [braiding_leftUnitor, unitors_equal]

end IsAddCommMonObj

variable {M : C} [AddMonObj M]

variable (M) in
@[reassoc (attr := simp)]
lemma AddMonObj.mul_mul_add_comm [IsAddCommMonObj M] :
    tensorμ M M M M ≫ (μ ⊗ₘ μ) ≫ μ = (μ ⊗ₘ μ) ≫ μ := by simp only [mon_tauto]

@[deprecated (since := "2025-09-09")] alias Mon_Class.mul_mul_add_comm := AddMonObj.mul_mul_add_comm

variable (M) in
@[reassoc (attr := simp)]
lemma AddMonObj.mul_mul_add_comm' [IsAddCommMonObj M] :
    tensorδ M M M M ≫ (μ ⊗ₘ μ) ≫ μ = (μ ⊗ₘ μ) ≫ μ := by simp only [mon_tauto]

@[deprecated (since := "2025-09-09")] alias Mon_Class.mul_mul_add_comm' := AddMonObj.mul_mul_add_comm'

end

section SymmetricCategory
variable [SymmetricCategory C] {M N W X Y Z : C} [AddMonObj M] [AddMonObj N]

instance [IsAddCommMonObj M] [IsAddCommMonObj N] : IsAddCommMonObj (M ⊗ N) where
  add_comm := by
    simp [← IsIso.inv_comp_eq, tensorμ, ← associator_inv_naturality_left_assoc,
      ← associator_naturality_right_assoc, SymmetricCategory.braiding_swap_eq_inv_braiding M N,
      ← tensorHom_def_assoc, -whiskerRight_tensor, -tensor_whiskerLeft, AddMonObj.tensorObj.add_def,
      ← MonoidalCategory.whiskerLeft_comp_assoc, -MonoidalCategory.whiskerLeft_comp]

end SymmetricCategory
end CategoryTheory
