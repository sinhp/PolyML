/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-! # List Arithmetic Categories

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

open Category Opposite Limits MonoidalCategory CartesianMonoidalCategory

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

open Endofunctor Algebra

/-
For an object `A` of a finite product product category `C`, an action of `A` on an object `S` is a
morphism `A ⊗ S → S`. The pairs `(S, A ⊗ S → S)` are objects of the category `Act A`, constructed as the category
of algebras for the left-tensoring endofunctor `A ⊗ -` on `C`. One may regard the objects of this
category as state-changing alphabet `A` acting on sets of states `S`.
-/
abbrev Act {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (A : C) := Algebra <| tensorLeft A

namespace Act

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

@[simp]
lemma hom {A : C} {σ σ' : Act A} {f : σ ⟶ σ'} : A ◁ f.1 ≫ σ'.str = σ.str ≫ f.1 := f.h

def forget {A : C} : Act A ⥤ C :=
  Algebra.forget (tensorLeft A)

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

class WithRecursion {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (A : C) where
  freeActionFunctor : C ⥤ Act A
  freeForgetAdj : freeActionFunctor ⊣ Act.forget

/-- An object `A` in a category `C` is called **recursive** if the forgetful functor from the
category of actions on `A` to `C` has a left adjoint. -/
class HasRecursion {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (A : C) where
  /-- The Act.forgetful functor from the category of actions to the category `C` has a
  left adjoint. -/
  adj : Functor.IsRightAdjoint (Act.forget : Act A ⥤ C)

variable (C)

/-- A category `C` is called **recursive** if every object `A` in `C` is recursive. -/
class Recursive (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] where
  withRec (A : C) : WithRecursion A

/-- A category `C` is called **recursive** if every object `A` in `C` is recursive. -/
class IsRecursive (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] where
  has_rec (A : C) : HasRecursion A

namespace IsRecursive

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [IsRecursive C]

instance (A : C) : Functor.IsRightAdjoint (Act.forget : Act A ⥤ C) :=
  (IsRecursive.has_rec A).adj

noncomputable
def freeActionFunctor (A : C) : C ⥤ Act A := Functor.leftAdjoint (Act.forget : Act A ⥤ C)

noncomputable
def freeForgetAdj (A : C) : freeActionFunctor A ⊣ Act.forget  :=
  Adjunction.ofIsRightAdjoint (Act.forget : Act A ⥤ C)

end IsRecursive

namespace Recursive

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C][Recursive C]

def freeActionFunctor (A : C) : C ⥤ Act A := (withRec A).freeActionFunctor

def freeForgetAdj (A : C) : freeActionFunctor A ⊣ Act.forget :=
  (withRec A).freeForgetAdj

/-- The mate of natural transformation `forget ⟶ map f ⋙ forget`. -/
def freeActionFunctorMapTriangle {A B : C} (f : A ⟶ B) :
    freeActionFunctor A ⟶ freeActionFunctor B ⋙ Act.map f :=
  mateEquiv (freeForgetAdj B) (freeForgetAdj A) |>.invFun <| Act.mapForgetTwoSquare f

theorem freeActionFunctorMapTriangle_id {A : C} :
    IsIso <| freeActionFunctorMapTriangle (𝟙 A) := by
  sorry  -- use some fact about mates of idenity to derive this
  -- need more API to use conjugateEquiv in the special case when Act.map (𝟙) ≅ 𝟭
  -- use the iso Act.map (𝟙) ≅ 𝟭 to promote the original mates diagram
  -- to a conjuage mate diagram apply the lemma
  --`conjugateEquiv_symm_iso` to construct an iso 2-cell between the
  -- left adjoints and then prove
  -- the resulting conjugate mate diagram is the same as the original mate diagram.
  -- perhpas refactor

/-- The paramtetrized list of `A` with the parameter `P`. -/
def plist (A P : C) := freeActionFunctor A ⋙ Act.forget |>.obj P

namespace plist

variable {A P : C}

/-r₀ : X ⟶ rec (A,X)-/
def nil : P ⟶ plist A P := freeForgetAdj A |>.unit |>.app P

/-r₁ : A × rec (A, X) ⟶ rec (A,X) -/
def cons : A ⊗ plist A P ⟶ plist A P :=
  freeActionFunctor A |>.obj P |>.str

/-- The recursor morphism obtained as an adjoint transpose. -/
def rec {Y : C} (f : P ⟶ Y) (g : A ⊗ Y ⟶ Y) : plist A P ⟶ Y :=
  Act.forget.map <| freeForgetAdj A |>.homEquiv P ⟨Y, g⟩ |>.invFun f

/- r₀ ≫ rec g f = f -/
@[reassoc (attr := simp)]
theorem rec_nil {Y : C} {f : P ⟶ Y} {g : A ⊗ Y ⟶ Y} :
    plist.nil ≫ plist.rec f g = f := by
  dsimp [rec, nil, Adjunction.homEquiv]
  simp only [Functor.map_comp, Adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components, comp_id]

@[reassoc (attr := simp)]
theorem rec_nil' {Y : C} {f : P ⟶ Y} {g : A ⊗ Y ⟶ Y} :
   A ◁ plist.nil ≫ A ◁ plist.rec f g = A ◁ f := by {
    ext : 1
    · simp_all only [assoc, whiskerLeft_fst]
    · simp_all only [assoc, whiskerLeft_snd, whiskerLeft_snd_assoc, rec_nil]
   }

open CategoryTheory.Adjunction

theorem rec_cons {Y : C} {f : P ⟶ Y} {g : A ⊗ Y ⟶ Y} :
    plist.cons ≫ plist.rec f g = A ◁ plist.rec f g ≫ g := by
  dsimp [rec, cons, Adjunction.homEquiv]
  simp only [Act.forget, Algebra.forget,← Act.hom, plist]

theorem rec_nil_cons_id : rec nil cons = 𝟙 (plist A P) := by {sorry

  }

/-- Covariant action of `plist` on morphisms of the first argument. -/
def map {B : C} (u : A ⟶ B) : plist A P ⟶ plist B P :=
  rec nil ((u ▷ (plist B P)) ≫ cons)

/-- Covariant action of `plist` on morphisms can be obtained as image of the component of the
natural transformation `Act.forget.map <| freeActionFunctorMapTriangle f` under the forgetful
functor `Act.forget : Act B ⥤ C`. -/
theorem map_nat_trans {B : C} {f : A ⟶ B} :
  map (P:= P) f = (Act.forget.map <| freeActionFunctorMapTriangle f |>.app P) := by
  dsimp [Adjunction.homEquiv,freeActionFunctorMapTriangle]
  simp only [Act.mapForgetTwoSquare,Act.mapForgetIsoSquare,Act.mapForgetIso]
  simp only [Functor.map_id, comp_id, id_comp]
  refine ((freeActionFunctor A).map ((freeForgetAdj B).unit.app P)).f ≫= ?_
  dsimp [Act.forget, forget_map, Act.map]
  simp only [Functor.map_id, id_f, id_comp]
  rfl

@[reassoc (attr := simp)]
theorem map_nil {B: C} {f : A ⟶ B} : (nil : P ⟶ plist A P) ≫ map f = nil := by
  simp only [map, rec_nil]

@[reassoc (attr := simp)]
theorem map_cons {B : C} {f : A ⟶ B} :
    (cons : A ⊗ plist A P ⟶ plist A P) ≫ map f =
    (A ◁ map f) ≫ (f ▷ plist B P) ≫ cons := by
  simp only [map, rec_cons]

lemma whisker_map_nil {B: C} {f : A ⟶ B} :
  (A ◁ plist.nil) ≫ (A ◁ plist.map f (P := P)) = (A ◁ plist.nil) := by
  aesop
  -- rw [← whiskerLeft_comp]
  -- simp only [map_nil]

lemma whisker_map_nil_right {B: C} {f : A ⟶ B} : (plist.nil ▷ P) ≫
(plist.map f (P := P) ▷ P) = (plist.nil ▷ P) := by
  ext : 1
  · simp_all only [assoc, whiskerRight_fst, whiskerRight_fst_assoc, map_nil]
  · simp_all only [assoc, whiskerRight_snd]

@[simp]
theorem map_id : map (𝟙 A) = 𝟙 (plist A P) := by simp [map, rec_nil_cons_id]

@[simp]
theorem map_comp {A B B' P : C} (u : A ⟶ B) (v : B ⟶ B') :
    plist.map (P := P) (u ≫ v) = plist.map u ≫ plist.map v := by
  dsimp [map]
  sorry


variable (P)

def functor : C ⥤ C where
  obj A := plist A P
  map := plist.map
  map_id _ := plist.map_id
  map_comp := plist.map_comp

variable {P}

open Category

@[simp]
/- The action morphism is unique. -/
theorem rec_uniq {A P C' : C} {f : P ⟶ C'} {g : A ⊗ C' ⟶ C'}
  (h : plist A P ⟶ C') (hh₁ : plist.nil ≫ h = f) (hh₂ : plist.cons ≫ h = A ◁ h ≫ g) :
    h = plist.rec f g := by {
      sorry
    }

/-- The comparision morphism `plist A (X ⊗ C') ⟶ (plist A X) ⊗ C`. -/
def cmp (A P C' : C) : plist A (P ⊗ C') ⟶ (plist A P) ⊗ C' :=
  plist.rec (plist.nil ▷ C') ((α_ _ _ _).inv ≫ (plist.cons ▷ C'))

/-- `plist` is functorial in parameter `X`. -/
def map' (A : C) {P P' : C} (f : P ⟶ P') : plist A P ⟶ plist A P' :=
  Act.forget.map <| freeActionFunctor A |>.map f

theorem map'_eq_rec {A P P' : C} {f : P ⟶ P'} :
    (plist.map' A f) = plist.rec (f ≫ plist.nil) plist.cons := by
  refine rec_uniq (Act.forget.map (freeActionFunctor A |>.map f)) ?_ ?_
  · simp only [nil, Adjunction.unit_naturality]
  · simp only [cons, Act.forget, forget_map, Act.hom]

theorem map'_comp {A : C} {P P' P'' : C} (f : P ⟶ P') (g : P' ⟶ P'') :
    plist.map' A (f ≫ g) = plist.map' A f ≫ plist.map' A g := by
  dsimp [plist.map']
  rw [Functor.map_comp]
  simp only [Functor.map_comp]

@[simp]
theorem map'_id (A : C) : plist.map' A (𝟙 _) = 𝟙 (plist A (𝟙_ C)) := by {
  dsimp [plist.map']
  simp only [Functor.map_id, comp_id, whiskerLeft_id, id_comp,
    plist.rec_uniq, plist.rec_nil]
  exact rfl}

@[simp]
theorem map'_id_tensor (A B : C) : plist.map' A (𝟙 (𝟙_ C ⊗ B)) =
   𝟙 (plist A (𝟙_ C ⊗ B)) := by
  dsimp [plist.map']
  simp only [Functor.map_id]
  rfl

@[simp]
theorem map'_id' (A : C) (P : C) : plist.map' A (𝟙 P) = 𝟙 (plist A P) := by
  dsimp [plist.map']
  simp only [Functor.map_id]
  rfl

instance map'_iso_of_iso {A P P' : C} (f : P ⟶ P') [h : IsIso f] :
    IsIso (plist.map' A f) := by
  have := h.out
  obtain ⟨finv, hfinvl, hfinvr⟩:= this
  constructor
  let inv : plist A P' ⟶ plist A P := by {
     apply map'
     exact finv
     }
  use inv
  constructor
  · unfold inv
    rw [← map'_comp]
    rw [hfinvl]
    simp only [map'_id', comp_id, whiskerLeft_id, id_comp, rec_uniq, rec_nil]
  · unfold inv
    rw [← map'_comp]
    rw [hfinvr]
    simp only [map'_id', comp_id, whiskerLeft_id, id_comp, rec_uniq, rec_nil]

end plist

/-- The list object defined as the recursive object
  with the terminal object as paramter `P`. -/
def list (A : C) : C := plist A (𝟙_ C)

namespace list

/- ε : 1 ⟶ list A -/
def nil {A : C} : 𝟙_ C ⟶ list A :=
  plist.nil (P := 𝟙_ C)

/- cons : A × list A ⟶ list A -/
def cons {A : C} : A ⊗ list A ⟶ list A :=
  plist.cons (P := 𝟙_ C)

/-- The weak recursion scheme for the list object. See `list.rec`
for the strong recursion scheme. -/
def rec' {A Y : C} (e : 𝟙_ C ⟶ Y) (f : A ⊗ Y ⟶ Y) : list A ⟶ Y :=
  plist.rec e f

def foldr {A Y : C} (f : A ⊗ Y ⟶ Y) (e : 𝟙_ C ⟶ Y) : list A ⟶ Y :=
  plist.rec e f

def foldl {A Y : C} (f : Y ⊗ A ⟶ Y) (e : 𝟙_ C ⟶ Y) : list A ⟶ Y :=
  plist.rec e ((β_ A Y).hom ≫ f)

def map {A B : C} (f : A ⟶ B) : list A ⟶ list B :=
  plist.map (P := 𝟙_ C) f

@[reassoc (attr := simp)]
theorem map_nil {A B : C} {f : A ⟶ B} :
    (list.nil : 𝟙_ C ⟶ list A) ≫ list.map f = plist.nil := by
  simp only [list.nil, list.map, plist.map_nil]

@[simp]
theorem map_cons {A B : C} {f : A ⟶ B} :
    (cons : A ⊗ list A ⟶ list A) ≫ map f =
    (A ◁ map f) ≫ (f ▷ list B) ≫ cons := by
  simp only [list, list.cons, list.map, plist.map_cons]

@[simp]
theorem map_comp {A B B' : C} (f : A ⟶ B) (g : B ⟶ B') :
    map (f ≫ g) = map f ≫ map g := by
  simp only [list.map, plist.map_comp]

@[simp]
theorem map_id {A : C} : list.map (𝟙 A) = 𝟙 (list A) := by
  simp only [list.map, plist.map_id, list]

def singleton {A : C} : A ⟶ list A :=
  (ρ_ (A)).inv ≫ (A ◁ (list.nil)) ≫ list.cons

end list

variable (C)

/-- The natural numbers object (NNO) defined as
  the list object of the terminal object. -/
def nno : C :=
  list (𝟙_ C)

@[inherit_doc] notation "N_" => nno

variable {C}

def nno.zero : 𝟙_ C ⟶ N_ C :=
  list.nil

def nno.succ : N_ C ⟶ N_ C :=
  (λ_ _).inv ≫ list.cons (A:= 𝟙_ C)

def nno.one : 𝟙_ C ⟶ N_ C :=
  nno.zero ≫ nno.succ

/-- The length of a list. -/
def list.len {A : C} : list A ⟶ N_ C :=
  list.map <| toUnit A

lemma len_eq_blah : list.cons ≫ list.len (C:=C) = A ◁ list.map (toUnit A) ≫ by {
  exact (toUnit A ▷ list (𝟙_ C)) ≫ list.cons (A := 𝟙_ C)} := by {
  dsimp [list.len]
  dsimp [list.cons]
  dsimp [list.map]
  rw [plist.map_cons]
  rfl}

/-- The length of a list, defined recursively. -/
def list.len' {A : C} : list A ⟶ N_ C := by
  apply list.rec' nno.zero
  apply CategoryTheory.CartesianMonoidalCategory.snd (X := A) (Y := N_ C ) ≫ nno.succ

/- len nil = 0 -/
lemma list_zero : list.nil (A:=A) ≫ list.len' = nno.zero (C := C) := by {
  dsimp [list.len']
  dsimp [nno.zero]
  dsimp [list.rec']
  dsimp [list.nil]
  rw [plist.rec_nil (f:= plist.nil) (g:= (snd A (N_ C) ≫ nno.succ))]}

/-- The tail of a list: removes the first element from a non-empty list. -/
def tail {A : C} : A ⊗ list A ⟶ list A := by {
  apply CategoryTheory.CartesianMonoidalCategory.snd A}

--len (cons x xs) = succ (len xs)
lemma len_cons  :
  list.cons ≫ list.len' = tail (A:=A) ≫ list.len' (C:=C) ≫ nno.succ := by {
    dsimp [list.len']
    dsimp [list.rec']
    dsimp [list.cons]
    rw [plist.rec_cons]
    simp only [whiskerLeft_snd_assoc]
    dsimp [tail]
    dsimp [list]}

open Category

/-- The length of the singleton list is `1`. -/
theorem list.singleton_len {A : C} :
  list.singleton ≫ list.len' = toUnit A ≫ nno.zero ≫ nno.succ := by {
  dsimp [list.singleton]
  rw [assoc]
  rw [assoc]
  rw [len_cons]
  rw [← assoc]
  rw [← assoc]
  rw [← assoc]
  rw [← assoc]
  refine ?_ =≫ nno.succ
  rw [← list_zero]
  dsimp [tail]
  dsimp [len']
  simp only [assoc, whiskerLeft_snd, rightUnitor_inv_snd_assoc]
  rfl}

end Recursive

open Recursive

-- class ListArithmetic' where
--   is_iso {A P Y : C} : IsIso (plist.cmp A P Y)

/-- A recursive category is list-arithmetic if the comparison morphisms `cmp A P Y` are
all isomorphisms. -/
class ListArithmetic (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] extends Recursive C where
  cmpInv (A P Y : C) : plist A P ⊗ Y ⟶ plist A (P ⊗ Y)
  hom_inv_id : plist.cmp A P Y ≫ cmpInv A P Y = 𝟙 _
  inv_hom_id : cmpInv A P Y ≫ plist.cmp A P Y = 𝟙 _

namespace ListArithmetic

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C][ListArithmetic C]

instance is_iso_instance {A P Y : C} : IsIso (plist.cmp A P Y) := by
  use cmpInv A P Y
  constructor
  rw [ListArithmetic.hom_inv_id]
  rw [ListArithmetic.inv_hom_id]

/-- In a list-arithmetic category, `plist A B` is isomorphic to `(list A) ⊗ B`. -/
def plistIsoTensor (A B : C) : plist A B ≅ list A ⊗ B where
  hom := plist.map' A (λ_ B).inv ≫ plist.cmp A (𝟙_ C) B
  inv := cmpInv A (𝟙_ C) B ≫ ((plist.map' A (λ_ B).hom))
  hom_inv_id := by
    refine (hom_comp_eq_id (plist.map' A (λ_ B).inv ≫ plist.cmp A (𝟙_ C) B)).mpr ?_
    have := ListArithmetic.inv_hom_id (A:=A) (P :=(𝟙_ C)) (Y := B)
    simp only [IsIso.inv_comp, IsIso.eq_comp_inv, assoc]
    refine Eq.symm (IsIso.inv_eq_of_inv_hom_id ?_)
    rw [← this]
    rw [assoc]
    rw [assoc]
    refine cmpInv A (𝟙_ C) B ≫= ?_
    rw [← assoc]
    rw [← plist.map'_comp]
    simp only [Iso.hom_inv_id]
    rw [plist.map'_id_tensor]
    simp only [comp_id, whiskerLeft_id, id_comp, plist.rec_uniq, plist.rec_nil]
  inv_hom_id := by
    refine (comp_hom_eq_id (plist.map' A (λ_ B).inv ≫ plist.cmp A (𝟙_ C) B)).mpr ?_
    have := ListArithmetic.hom_inv_id (A:=A) (P :=(𝟙_ C)) (Y := B)
    simp only [IsIso.inv_comp, IsIso.eq_comp_inv, assoc]
    refine Eq.symm (IsIso.inv_eq_of_hom_inv_id ?_)
    rw [← this]
    rw [← plist.map'_comp]
    simp only [Iso.hom_inv_id, plist.map'_id_tensor, comp_id, whiskerLeft_id, id_comp,
      plist.rec_uniq, plist.rec_nil]

  --asIso (plist.map' A (λ_ P).inv ≫ plist.cmp A (𝟙_ C) P)
/-- Recursion scheme for the list object in a list-arithmetic category. -/
def list.rec {A P Y : C} (e : P ⟶ Y) (a : A ⊗ Y ⟶ Y) : list A ⊗ P ⟶ Y :=
  (plistIsoTensor A P).inv ≫ plist.rec e a

def list.foldr {A P Y : C} (a : A ⊗ Y ⟶ Y) (e : P ⟶ Y) : list A ⊗ P ⟶ Y :=
  list.rec e a

def nno.rec {P Y : C} (e : P ⟶ Y) (a : Y ⟶ Y) : N_ C ⊗ P ⟶ Y :=
  list.rec e ((λ_ Y).hom ≫ a)

namespace list

theorem rec_nil {A P Y : C} {f : P ⟶ Y} {g : A ⊗ Y ⟶ Y} :
  ((λ_ P).inv ≫ list.nil ▷ P) ≫ list.rec f g = f := by {
  dsimp [rec]
  nth_rw 2 [← plist.rec_nil (f := f) (g := g)]
  rw [← assoc]
  refine ?_ =≫ plist.rec f g
  rw [assoc]
  refine (Iso.inv_comp_eq (λ_ P)).mpr ?_
  refine (Iso.comp_inv_eq (plistIsoTensor A P)).mpr ?_
  simp only [assoc]
  dsimp [list.nil]
  dsimp [plistIsoTensor]
  rw [plist.map'_eq_rec]
  dsimp [plist.cmp]
  simp only [plist.rec_nil, plist.rec_nil_assoc, assoc, Iso.hom_inv_id_assoc]}

/-- Appends two lists. -/
def append {A : C} : (list A ⊗ list A) ⟶ list A :=
  list.rec (𝟙 _) (list.cons)

-- [] ++ xs= xs
theorem nil_append {A : C} : list.nil ▷ list A ≫ append = (λ_ (list A)).hom := by
  refine (Iso.inv_comp_eq_id (λ_ (list A))).mp ?_
  rw [← assoc]
  dsimp [append]
  apply rec_nil

/-- If two morphisms `f, g : plist A P ⟶ Y` agree on `nil` and `cons`, then they are equal. -/
lemma plist.ext {A P Y : C} {f g : plist A P ⟶ Y}
  (h₀ : plist.nil ≫ f = plist.nil ≫ g)
  (h₁ : plist.cons ≫ f = plist.cons ≫ g) : f = g := by {sorry}

--xs ++ [] = xs
theorem append_nil {A : C} : list A ◁ list.nil ≫ append = (ρ_ (list A)).hom := by
  refine (Iso.comp_inv_eq_id (ρ_ (list A))).mp ?_
  dsimp [append]
  dsimp [rec]
  rw [← assoc]
  dsimp [list.cons]
  rw [← plist.rec_uniq (C:=C) (f := 𝟙 (list A)) (g := plist.cons) (h := ?_)]
  · sorry
  · sorry
  · sorry
  · sorry
    -- apply plist.map'
    -- exact toUnit (list A)

-- (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
theorem append_assoc {A : C} : list.append ▷ list A ≫ append =
  (α_ (list A) (list A) (list A)).hom ≫ list A ◁ list.append ≫ list.append := by {
  dsimp [append]
  dsimp [rec]
  rw [← assoc]
  dsimp [list.cons]
  rw [← plist.rec_uniq (C:=C) (f := 𝟙 (list A)) (g := plist.cons) (h := ?_)]
  · sorry
  · sorry
  · sorry
  · sorry
  }

-- map f (xs ++ ys) = map f xs ++ map f ys
theorem map_append {A B : C} {f : A ⟶ B} :
  list.append ≫ list.map f = ((list.map f) ⊗ₘ (list.map f)) ≫ list.append := by
  rw [tensorHom_def]
  sorry

/-- Reverses a list, i.e. the list with the elements in reverse order. -/
def rev {A : C} : list A ⟶ list A :=
  list.rec' list.nil ((list.singleton ▷ list A) ≫ (β_ _ _).hom ≫ list.append)

/- rev_nil [] = [] -/
lemma rev_nil {A : C} :
  list.nil (A := A) ≫ list.rev (A := A) = list.nil (A := A) := by {
  dsimp [rev]
  dsimp [list.nil]
  dsimp [list.rec']
  simp only [plist.rec_nil]}

/- [x] as x :: [] -/
lemma sing_cons_empty {A : C} : list.singleton (A := A) =
    (ρ_ A).inv ≫ (A ◁ list.nil) ≫ list.cons := by
  dsimp [list.singleton, list.cons, list.nil]

/-⁠[x] ++ xs = x :: xs-/
lemma singleton_append_eq_cons {A : C} : (list.singleton ▷ list A) ≫ (β_ _ _).hom ≫
   list.append  = list.cons (A := A) := by {
  dsimp [list.cons, rec]
  dsimp [append]
  dsimp [list.singleton]
  rw [← assoc]
  simp only [comp_whiskerRight]
  rw [assoc]
  dsimp [list.cons]
  have := plist.rec_cons (f := (𝟙 (list A))) (g := plist.cons)
  sorry
  }

/- rev [x] = [x] -/
lemma rev_singleton_eq_singleton {A : C} :
  list.singleton (A := A) ≫ list.rev (A := A) = list.singleton (A := A) := by {
  nth_rw 1 [list.singleton]
  dsimp [rev]
  dsimp [list.rec']
  rw [assoc, assoc]
  dsimp [list.cons]
  rw [plist.rec_cons]
  dsimp [list.nil]
  simp only [← assoc, plist.rec_nil']
  simp only [assoc,singleton_append_eq_cons ]
  dsimp [list.singleton]
  rfl}

/- rev (xs ++ ys) = rev ys ++ rev xs -/
lemma rev_append {A : C} : list.append (A := A) ≫ list.rev (A := A) =
  (list.rev (A:=A) ⊗ₘ list.rev (A := A)) ≫ list.append (A := A) := by {
  dsimp [rev]
  dsimp [list.rec']
  rw [singleton_append_eq_cons ]
  have map_append {A B : C} {f : A ⟶ B} :
  list.append ≫ list.map f = ((list.map f) ⊗ₘ (list.map f)) ≫ list.append := map_append
  dsimp [list.map] at map_append
  dsimp [plist.map] at map_append
  let f : A ⟶ A := 𝟙 (A)
  simp only at f
  have := map_append  (f := f)
  dsimp [list.nil,list.cons]
  simp_all only [id_whiskerRight, id_comp, f]}

/-rev (rev (x :: xs)) = rev (rev xs ++ [x])-/
lemma rev_rev_cons_eq_rev_append_singleton {A : C} :
  plist.cons ≫ list.rev ≫ list.rev (C:=C) =
    (((list.singleton ▷ list A) ≫ (β_ _ _).hom ≫ list.append ≫ list.rev)) ≫ list.rev := by {
  rw [← assoc]
  refine ?_ =≫ rev
  have := singleton_append_eq_cons (C:=C) (A:=A)
  dsimp [list.cons] at this
  rw [← this]
  simp only [assoc]
}

/-rev rev (xs ++ [x]) = rev [x] ++ rev (rev xs)-/
lemma rev_rev_append_singleton_distrib {A : C} :
  (((list.singleton ▷ list A)  ≫ (β_ _ _).hom ≫ list.append ≫ list.rev)) ≫ list.rev =
  ((list.singleton (A := A) ▷ list A) ≫  (rev ▷ list A) ≫  (β_ _ _).hom ≫
     list.append (A := A) ≫ list.rev ≫ list.rev (A := A)) := by {
  rw [assoc]
  have H := (rev_singleton_eq_singleton (C:=C) (A:=A)).symm
  have :  list.singleton ▷ list A ≫ ((β_ _ _).hom ≫  append ≫ rev) ≫ rev =
     list.singleton ▷ list A ≫ ((β_ _ _).hom ≫ append ≫ rev ≫ rev) := by {simp only [assoc]}
  rw [this]
  have : list.singleton ▷ list A ≫ rev ▷ list A ≫ (β_ _ _).hom ≫ append ≫ rev ≫ rev =
    (list.singleton ▷ list A ≫ rev ▷ list A) ≫ ((β_ _ _).hom ≫ append ≫ rev ≫ rev) := by {simp only [assoc]}
  rw [this]
  refine ?_ =≫ ((β_ _ _).hom ≫append ≫ rev ≫ rev)
  nth_rw 1 [H]
  simp only [comp_whiskerRight]}

/-rev [x] ++ rev (rev xs) = rev [x] ++ xs-/
lemma rev_singleton_append_rev_rev_eq_rev_singleton_append_id {A : C} :
  ((list.singleton (A := A) ▷ list A) ≫ (rev ▷ list A) ≫ (β_ _ _).hom ≫
     list.append (A := A) ≫ list.rev ≫ list.rev (A := A)) =
  ((list.singleton ▷ list A)) ≫ (rev ▷ list A) ≫ (β_ _ _).hom ≫ append (C := C) (A := A) := by {
  have H := (rev_singleton_eq_singleton (C:=C) (A:=A)).symm
  sorry
  }
-- Then
-- rev (xs ++ [x])
-- = rev [x] ++ rev (rev xs)
-- = rev [x] ++ xs

-- Note
-- - rev  [x] = [x]
-- - ⁠[x] ++ xs = x :: xs

/-- list.rev is an involution, i.e. `list.rev ≫ list.rev = 𝟙`. -/
theorem rev_rev {A : C} : list.rev ≫ list.rev = 𝟙 (list A) := by {
  apply plist.ext
  · dsimp [rev]
    dsimp [list.rec']
    simp only [plist.rec_nil_assoc]
    dsimp [list]
    simp only [plist.rec_nil, comp_id, whiskerLeft_id, id_comp, plist.rec_uniq]
    dsimp [list.nil]
    simp only [plist.rec_nil]
  · rw [rev_rev_cons_eq_rev_append_singleton]
    simp only [rev_rev_append_singleton_distrib]
    rw [rev_singleton_append_rev_rev_eq_rev_singleton_append_id]
    have H := (rev_singleton_eq_singleton (C:=C) (A:=A)).symm
    rw [← assoc]
    rw [← assoc]
    simp only [assoc, BraidedCategory.braiding_naturality_left,
      BraidedCategory.braiding_naturality_left_assoc]
    have : (β_ A (list A)).hom ≫ list A ◁ list.singleton ≫ list A ◁ rev ≫ append=
     (β_ A (list A)).hom ≫ (list A ◁ list.singleton ≫ list A ◁ rev) ≫ append := by {simp only [assoc]}
    rw [this]
    --simp only [singleton_append_eq_cons]
    -- dsimp [list.cons]
    -- exact Eq.symm (comp_id plist.cons)
    sorry
    }

/-- Concatenates a list of lists into a single list, preserving the order of the elements. -/
def flatten {A : C} : list (list A) ⟶ list A :=
  list.rec' list.nil list.append

end list

instance : Recursive (Type u) where
  withRec := sorry

/-- The category of types is list-arithmetic. -/
instance : ListArithmetic (Type u) where
  cmpInv A P Y := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

end ListArithmetic

/-
In the presence finite coproducts, `list α` is the
initial algebra for the polynomial functor
`P ↦ 1 + α × P`. The unique algebra map from `(List α, [n,c])` to
`(S,[s₀,s])` is the `foldr` function after transposition:
`foldr : (α → β → β) → β → List α → β`
satisfying
`foldr s s₀ n = s₀` and
`foldr s s₀ (c x xs) = s x (foldr s s₀ xs)`
-/


/-
Extra challenge:
Show that in the category of small categories,
an object with recursion is a monoidal category.
-/


/-
We show that in a list-arithmetic category, the list object is
the free monoid object.
-/
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [ListArithmetic C]

open Recursive ListArithmetic

instance mon_class (A : C) : Mon_Class (list A) where
  one := list.nil
  mul := list.append
  one_mul := list.nil_append
  mul_one := list.append_nil
  mul_assoc := list.append_assoc

/--
The monoid structure on the list object in a list-arithmetic category.
-/
instance List.monoid (A : C) : Mon_ C where
  X := list A
  -- one := list.nil
  -- mul := list.append
  -- one_mul := list.nil_append
  -- mul_one := list.append_nil
  -- mul_assoc := list.append_assoc

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

open Recursive ListArithmetic
