/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.FintypeCat


/-
In category theory, the notion of parameterized list object models the list type, directly generalising Lawvere’s notion of NNO (Natural Numbers Object)

A **list object** on an object `A` in a category with finite products consists of an object `list A` and morphisms `nil : ⊤_C → list A` and `cons : A × list A  ⟶ list A`
which is initial among such data.

Such a structure is a **parameterized list object** whenever it is parametrized initial, i.e. it is initial among the data of `(P → L ← P × L)` for some parameter object `P` in the category.

In cartesian closed categories, these two notions coincide.
-/

universe u v

noncomputable section
namespace CategoryTheory

open Functor Opposite Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]

attribute [local instance] monoidalOfChosenFiniteProducts



open Endofunctor

/-
For an object `A` of a finite product product category `C`, an action of `A` on an object `S` is a morphism `A ⊗ S → S`. The pairs `(S, A ⊗ S → S)` are objects of the category `Act A`, constructed as the category of algebras for the left-tensoring endofunctor `A ⊗ -` on `C`. One may regard the objects of this category as state-changing alphabet `A` acting on sets of states `S`.
-/
abbrev Act (A : C) := Algebra <| tensorLeft A

def actFunctor {A B : C} (f : A ⟶ B) : Act B ⥤ Act A :=
  Algebra.functorOfNatTrans <| curriedTensor C |>.map <| f

namespace Act

def forget {A : C} : Act A ⥤ C :=
  Algebra.forget (tensorLeft A)

end Act


open Act

variable (C)

class Recursive where
  /-- The forgetful functor from the category of actions to the category `C` has a left adjoint. -/
  adj (A : C) : IsRightAdjoint (Act.forget : Act A ⥤ C)

namespace Recursive

variable {C} [Recursive C]

instance (A : C) : IsRightAdjoint (Act.forget : Act A ⥤ C) :=
  Recursive.adj A

def freeActionFunctor (A : C) : C ⥤ Act A := leftAdjoint (Act.forget : Act A ⥤ C)

def freeForgetAdj (A : C) : freeActionFunctor A ⊣ Act.forget  := Adjunction.ofIsRightAdjoint (Act.forget : Act A ⥤ C)

/-- The recursive object of `A` with parameter `P` .-/
def recObj (A P : C) : C := freeActionFunctor A ⋙ Act.forget |>.obj P

def cons {A P : C} : A ⊗ recObj A P ⟶ recObj A P :=
  freeActionFunctor A |>.obj P |>.str

def nil {A P : C} : P ⟶ recObj A P := freeForgetAdj A |>.unit |>.app P

/-- The recursor morphism obtained as an adjoint transpose. -/
def recursor {A P Y : C} (f : P ⟶ Y) (a : A ⊗ Y ⟶ Y) : recObj A P ⟶ Y :=
  Act.forget |>.map (freeForgetAdj A |>.homEquiv P ⟨Y, a⟩ |>.invFun f)

theorem recursor_nil {A P Y : C} {f : P ⟶ Y} {a : A ⊗ Y ⟶ Y} :
    nil ≫ recursor f a = f := by
  sorry

theorem recursor_cons {A P Y : C} {f : P ⟶ Y} {a : A ⊗ Y ⟶ Y} :
    cons ≫ recursor f a = A ◁ (recursor f a) ≫ a := by
  sorry

theorem recursor_uniq {A P Y : C} {f : P ⟶ Y} {a : A ⊗ Y ⟶ Y} (g : recObj A P ⟶ Y)
    (hg₁ : nil ≫ g = f) (hg₂ : cons ≫ g = A ◁ g ≫ a) : g = recursor f a := by
  sorry

variable [HasTerminal C]

/-- The list object defined as the recursive object with the terminal object as paramter `P`. -/
def list (A : C) := recObj A (⊤_C)

def list.nil (A : C) : ⊤_C ⟶ list A :=
  Recursive.nil (P := ⊤_C)

def list.cons (A : C) : A ⊗ list A ⟶ list A :=
  Recursive.cons (P := ⊤_C)

def cmp (A P Y : C) : recObj A (P ⊗ Y) ⟶ (recObj A P) ⊗ Y :=
  recursor (nil ▷ Y) ((α_ _ _ _).inv ≫ (cons ▷ Y))

-- theorem cmp_nil : ∀ {A P Y : C}, cmp A P Y ≫ (list.nil A ▷ Y) = nil ▷ Y := by
--   intros
--   apply recursor_nil

variable (C)

/-- A recursive category is list-arithmetic if the comparison morphisms `cmp A P Y` are
all isomorphisms. -/
class ListArithmetic where
  is_iso : ∀ {A P Y : C}, IsIso (cmp A P Y)

def iso [ListArithmetic C] [HasTerminal C] {A P : C} : recObj A P ≅ (list A) ⊗ P :=
  sorry

instance : ChosenFiniteProducts (Type u) := sorry

instance : Recursive (Type u) where
  adj A := sorry

/-- The category of types is list-arithmetic. -/
instance : ListArithmetic (Type u) where
  is_iso := by
    sorry

end Recursive



/- Show that
`list α` is the initial algebra for the polynomial functor `P ↦ 1 + α × P` in
the category of types. The unique algebra map from (List α, [n,c]) to
(S,[s₀,s]) is the foldr function after transposition.
[]
`foldr : (α → β → β) → β → List α → β`
satisfying
`foldr s s₀ n = s₀` and
`foldr s s₀ (c x xs) = s x (foldr s s₀ xs)`
-/
