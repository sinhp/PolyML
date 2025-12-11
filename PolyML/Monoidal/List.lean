/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq


/-!
# List Arithmetic Categories

In category theory, the notion of parameterized list object models the list type, directly
generalising Lawvere’s notion of NNO (Natural Numbers Object)

A **list object** on an object `A` in a category with finite products consists of an object `list A`
and morphisms `nil : 𝟙_ C → list A` and `cons : A × list A  ⟶ list A`
which is initial among such data.

Such a structure is a **parameterized list object** whenever it is parametrized initial, i.e. it is initial
among the data of `(P → L ← P × L)` for some parameter object `P` in the category.

In cartesian closed categories, these two notions coincide.

## Implementation notes

- We use a high-level definition of parameterized list object based on existence of a left adjoint to the
forgetful functor from the category of actions to the underlying category `C`.
The advantage of this definition is that it gives a compact formulation of the universal property of the
list object from which the recursion scheme can be derived thus enabling us to define all the important list maps.
Such categories are called **recursive categories**. We can already define list maps such as `map`, `foldr` in recursive categories.

- The condition requiring the morphism `plist A (P ⊗ Y) ⟶ (plist A P) ⊗ Y` to be an isomorphism for all
objects `A, P, Y` is equivalent to the requirment that the recursion in `C` is preserved when
pulled back to the slice categories `C / P` for all `P`.

- Although parameterized list objects are defined in finite product categories, the well-behaved recursion
scheme is only available in **list-arithmetic categories**, i.e. in categories with chosen finite
products where the comparison morphisms `plist.cmp` are isomorphisms.

- In list-arithmetic categories, we can define additional list maps such as `append` and `flatten`.
-/


universe u v

namespace CategoryTheory

open Category Opposite Limits MonoidalCategory

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

open Endofunctor Algebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

class IsPList (A : C) (L : C) (nil : 𝟙_ C ⟶ L) (cons : A ⊗ L ⟶ L) where
  prc {P B : C} (f : P ⟶ B) (g : A ⊗ B ⟶ B) : L ⊗ P ⟶ B
  nil_prc {P B : C} {f : P ⟶ B} {g : A ⊗ B ⟶ B} :
    (nil ▷ P) ≫ prc f g = (λ_ P).hom ≫ f
  cons_prc {P B : C} {f : P ⟶ B} {g : A ⊗ B ⟶ B} :
    (α_ _ _ _).inv ≫ (cons ▷ P) ≫ prc f g = (A ◁ prc f g) ≫ g
  prc_uniq {P B : C} {f : P ⟶ B} {g : A ⊗ B ⟶ B} (r : L ⊗ P ⟶ B)
    (h_nil : (nil ▷ P) ≫ r = (λ_ P).hom ≫ f)
    (h_cons: (α_ _ _ _).inv ≫ (cons ▷ P) ≫ r =  A ◁ r ≫ g) : r = prc f g

attribute [reassoc (attr := simp)] IsPList.nil_prc IsPList.cons_prc

class PList (A : C) where
  L : C
  nil : 𝟙_ C ⟶ L
  cons (A) : A ⊗ L ⟶ L
  /-- The parameterized list object satisfies the properties of a left parameterized natural number object. -/
  [isPList : IsPList A L nil cons]

attribute [instance] PList.isPList

abbrev PList.prc {A : C} [PList A] {P B : C} (f : P ⟶ B) (g : A ⊗ B ⟶ B) :
    PList.L A ⊗ P ⟶ B :=
  IsPList.prc PList.nil (PList.cons A) f g

/-
For an object `A` of a finite product product category `C`, an action of `A` on an object `S` is a
morphism `A ⊗ S → S`. The pairs `(S, A ⊗ S → S)` are objects of the category `Act A`, constructed as the category
of algebras for the left-tensoring endofunctor `A ⊗ -` on `C`. One may regard the objects of this
category as state-changing alphabet `A` acting on sets of states `S`.
-/
abbrev Act [MonoidalCategory C] (A : C) := Algebra <| tensorLeft A

namespace Act

@[simp]
theorem hom {A : C} {σ σ' : Act A} {f : σ ⟶ σ'} : A ◁ f.1 ≫ σ'.str = σ.str ≫ f.1 := f.h

@[simps! +simpRhs obj map]
def forget {A : C} : Act A ⥤ C := Algebra.forget (tensorLeft A)

/-- `Act` is functorial. -/
def map {A B : C} (f : A ⟶ B) : Act B ⥤ Act A :=
  Algebra.functorOfNatTrans <| curriedTensor C |>.map <| f

def map_id {A : C} : map (𝟙 A) ≅ 𝟭 _ := by
  simp only [map]
  simp only [Functor.map_id]
  apply functorOfNatTransId

/-- `Act.functor` commutes with forgetful functor `Act.forget`. -/
theorem map_forget_eq {A B : C} (f : A ⟶ B) : map f ⋙ forget = forget  := by
  fapply Functor.ext
  · simp [forget, map]
  · aesop_cat

/-- Promoting the equality `map_forget_eq` of functors to an isomorphism. -/
def mapForgetIso {A B : C} (f : A ⟶ B) : map f ⋙ forget ≅ forget  :=
  eqToIso <| map_forget_eq f

/-- Making the iso-triangle `mapForgetIso` into an iso-square:
```
          Act A  --.forget A -> C
             ↑                  |
     .map f  |         ≅        | 𝟭
             |                  |
          Act B  --.forget B -> C
```
We use the mate of this iso-square to obtain the functoriality of `plist` in its first argument.
 -/
def mapForgetIsoSquare {A B : C} (f : A ⟶ B) : map f ⋙ forget ≅ forget ⋙ 𝟭 C := by
  let iso := mapForgetIso f
  nth_rewrite 2 [← Functor.comp_id (forget)] at iso
  exact iso

/-- The natural transformation `forget ⋙ 𝟭 C ⟶ map f ⋙ forget`. -/
def mapForgetTwoSquare {A B : C} (f : A ⟶ B) :
    TwoSquare forget (map f) (𝟭 C) forget :=
  (mapForgetIsoSquare f).inv

end Act

open IsPList

/-- An object `A` in a category `C` is said to have **recursion** if there is a functor from `C` to
the category of left `A`-actions which is left adjoint to the forgetful functor. -/
class WithRecursion (A : C) where
  freeActionFunctor (A) : C ⥤ Act A
  freeForgetAdj (A) : freeActionFunctor ⊣ Act.forget

/-- The left `A`-action on `PList A ⊗ P`. -/
@[simps! +simpRhs a str]
def PList.act (A : C) [PList A] (P : C) : Act A where
  a := PList.L A ⊗ P
  str := (α_ _ _ _).inv ≫ PList.cons A ▷ P

/-- A list object provides a left adjoint to the forgetful functor from `Act A` to `C`. -/
instance withRecursionOfPList {A : C} [PList A] : WithRecursion A where
  freeActionFunctor := {
    obj P := PList.act A P
    map {P Q} φ := {
      f := PList.L A ◁ φ
      h := by
        simp only [PList.act_a, curriedTensor_obj_obj, curriedTensor_obj_map, PList.act_str, assoc]
        rw [associator_inv_naturality_right_assoc, ← whisker_exchange]
    }
  }
  freeForgetAdj.unit.app P := (λ_ _).inv ≫ (PList.nil) ▷ P
  freeForgetAdj.counit.app β := {
    f := prc (nil := PList.nil) (cons := PList.cons A) (𝟙 (β.a)) β.str
    h := by simp }
  freeForgetAdj.unit.naturality P Q φ := by
    simp
    sorry
  freeForgetAdj.counit.naturality β γ f := by
    simp
    sorry

section

open PList

variable {A : C} [PList A] {P : C}

open WithRecursion

@[simp]
theorem withRecursionOfPList.freeActionFunctor_forget_obj :
    (freeActionFunctor A ⋙ Act.forget).obj P = PList.L A ⊗ P :=
  rfl

@[simp]
theorem withRecursionOfPList.freeForgetAdj_unit_app :
    (freeForgetAdj A |>.unit).app P = (λ_ _).inv ≫ (PList.nil) ▷ P :=
  rfl

@[simp]
theorem withRecursionOfPList.freeActionFunctor_obj_str :
    (freeActionFunctor A |>.obj P).str = (α_ _ _ _).inv ≫ PList.cons A ▷ P :=
  rfl

@[simp]
theorem withRecursionOfPList.forgetMap_freeForgetAdj_homEquiv {B : C} (f : P ⟶ B) (g : A ⊗ B ⟶ B) :
    (Act.forget.map <| freeForgetAdj A |>.homEquiv P ⟨B, g⟩ |>.invFun f) =
    prc f g := by
  sorry

@[simp]
theorem withRecursionOfPList.freeActionFunctor_map {Q : C} (φ : P ⟶ Q) :
    (freeActionFunctor A |>.map φ).f =
      prc (φ ≫ (λ_ Q).inv ≫ PList.nil ▷ Q) ((α_ _ _ _).inv ≫ PList.cons A ▷ Q) := by
  sorry

end

namespace PList

open IsPList

variable {A : C} [PList A] {P : C}

theorem prc_nil_cons_id : prc ((λ_ P).inv ≫ PList.nil ▷ P) ((α_ _ _ _).inv ≫ PList.cons A ▷ P) = 𝟙 (PList.L A ⊗ P) :=
  sorry


end PList

end CategoryTheory
