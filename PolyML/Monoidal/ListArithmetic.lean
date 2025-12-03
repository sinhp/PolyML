/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Types.Basic

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

variable {C : Type u} [Category.{v} C]

/-
For an object `A` of a finite product product category `C`, an action of `A` on an object `S` is a
morphism `A ⊗ S → S`. The pairs `(S, A ⊗ S → S)` are objects of the category `Act A`, constructed as the category
of algebras for the left-tensoring endofunctor `A ⊗ -` on `C`. One may regard the objects of this
category as state-changing alphabet `A` acting on sets of states `S`.
-/
abbrev Act [MonoidalCategory C] (A : C) := Algebra <| tensorLeft A

namespace Act

variable [MonoidalCategory C]

@[simp]
theorem hom {A : C} {σ σ' : Act A} {f : σ ⟶ σ'} : A ◁ f.1 ≫ σ'.str = σ.str ≫ f.1 := f.h

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

class WithRecursion [MonoidalCategory C] (A : C) where
  freeActionFunctor : C ⥤ Act A
  freeForgetAdj : freeActionFunctor ⊣ Act.forget

/-- An object `A` in a category `C` is called **recursive** if the forgetful functor from the
category of actions on `A` to `C` has a left adjoint. -/
class HasRecursion [MonoidalCategory C] (A : C) where
  /-- The Act.forgetful functor from the category of actions to the category `C` has a
  left adjoint. -/
  adj : Functor.IsRightAdjoint (Act.forget : Act A ⥤ C)

variable (C)

/-- A category `C` is called **recursive** if every object `A` in `C` is recursive. -/
class Recursive [MonoidalCategory C] where
  withRec (A : C) : WithRecursion A

/-- A category `C` is called **recursive** if every object `A` in `C` is recursive. -/
class IsRecursive [MonoidalCategory C] where
  has_rec (A : C) : HasRecursion A

namespace IsRecursive

variable [MonoidalCategory C] [IsRecursive C]

instance (A : C) : Functor.IsRightAdjoint (Act.forget : Act A ⥤ C) :=
  (IsRecursive.has_rec A).adj

variable {C}

noncomputable
def freeActionFunctor (A : C) : C ⥤ Act A := Functor.leftAdjoint (Act.forget : Act A ⥤ C)

noncomputable
def freeForgetAdj (A : C) : freeActionFunctor A ⊣ Act.forget  :=
  Adjunction.ofIsRightAdjoint (Act.forget : Act A ⥤ C)

end IsRecursive

namespace Recursive

variable {C} [MonoidalCategory C] [Recursive C]

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
  -- to a conjuage mate diagram apply the theorem
  --`conjugateEquiv_symm_iso` to construct an iso 2-cell between the
  -- left adjoints and then prove
  -- the resulting conjugate mate diagram is the same as the original mate diagram.
  -- perhpas refactor

end Recursive

variable {C}

/-- The paramtetrized list of `A` with the parameter `P`. -/
def plist [MonoidalCategory C] [Recursive C] (A P : C) :=
  Recursive.freeActionFunctor A ⋙ Act.forget |>.obj P

namespace plist

open Recursive

variable [MonoidalCategory C] [Recursive C] {A P : C}

/-r₀ : X ⟶ rc (A,X)-/
def nil : P ⟶ plist A P := freeForgetAdj A |>.unit |>.app P

/-r₁ : A × rc (A, X) ⟶ rc (A,X) -/
def cons : A ⊗ plist A P ⟶ plist A P :=
  freeActionFunctor A |>.obj P |>.str

/-- The recursor morphism obtained as an adjoint transpose. -/
def rc {Y : C} (init : P ⟶ Y) (action : A ⊗ Y ⟶ Y) : plist A P ⟶ Y :=
  Act.forget.map <| freeForgetAdj A |>.homEquiv P ⟨Y, action⟩ |>.invFun init

/-- `plist` is functorial in the parameter `P`. -/
def map' (A : C) {P P' : C} (f : P ⟶ P') : plist A P ⟶ plist A P' :=
  Act.forget.map <| freeActionFunctor A |>.map f

theorem map'_comp {A : C} {P P' P'' : C} (f : P ⟶ P') (g : P' ⟶ P'') :
    plist.map' A (f ≫ g) = plist.map' A f ≫ plist.map' A g := by
  dsimp [plist.map']
  rw [Functor.map_comp]
  simp only [Functor.map_comp]

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
  obtain ⟨finv, hfinvl, hfinvr⟩:= h.out
  use (map' _ finv)
  constructor
  · rw [← map'_comp, hfinvl, map'_id']
  · rw [← map'_comp, hfinvr, map'_id']

/- r₀ ≫ rc action init = init -/
@[reassoc (attr := simp)]
theorem nil_rc {Y : C} {init : P ⟶ Y} {action : A ⊗ Y ⟶ Y} :
    plist.nil ≫ plist.rc init action = init := by
  dsimp [rc, nil, Adjunction.homEquiv]
  simp only [Functor.map_comp, Adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components, comp_id]

@[reassoc (attr := simp)]
theorem whiskerLeft_nil_whiskerLeft_rc {Y : C} {init : P ⟶ Y} {action : A ⊗ Y ⟶ Y} :
    A ◁ plist.nil ≫ A ◁ plist.rc init action = A ◁ init := by
  rw [← whiskerLeft_comp A, nil_rc]

@[reassoc (attr := simp)]
theorem whiskerRight_nil_whiskerRight_rc {Y : C} {init : P ⟶ Y} {action : A ⊗ Y ⟶ Y} :
    plist.nil ▷ A ≫ plist.rc init action ▷ A = init ▷ A := by
  rw [← comp_whiskerRight _ _ A, nil_rc]

open CategoryTheory (Adjunction)

theorem cons_rc {Y : C} {init : P ⟶ Y} {action : A ⊗ Y ⟶ Y} :
    plist.cons ≫ plist.rc init action = A ◁ plist.rc init action ≫ action := by
  dsimp [rc, cons, Adjunction.homEquiv]
  simp only [Act.forget, Algebra.forget,← Act.hom, plist]

theorem whiskerLeft_cons_whiskerLeft_rc {Y : C} {init : P ⟶ Y} {action : A ⊗ Y ⟶ Y} :
    A ◁ plist.cons ≫ A ◁ plist.rc init action = A ◁ (A ◁ plist.rc init action ≫ action) := by
  rw [← whiskerLeft_comp A, cons_rc]

theorem whiskerRight_cons_whiskerRight_rc {Y : C} {init : P ⟶ Y} {action : A ⊗ Y ⟶ Y} :
    plist.cons ▷ A ≫ plist.rc init action ▷ A = (A ◁ plist.rc init action ≫ action) ▷ A := by
  rw [← comp_whiskerRight _ _ A, cons_rc]

-- *SH: not needed anymore*
/--
If `(F, G, η, ε)` is an adjunction between categories `C` and `D`, then for each
`X : C` and `Y : D`, there is a bijection between morphisms `φ : F.obj X ⟶ Y`
and `ψ : X ⟶ G.obj Y`, given by the adjunction hom-set equivalence.
This correspondence is unique.

So if two morphisms `f, g : F.obj X ⟶ Y` correspond to the same `X ⟶ G.obj Y`, then they must be equal.
-/
theorem adjunction_hom_equiv_unique
  {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X : C} {Y : D} :
  Function.Bijective (adj.homEquiv X Y) :=
  (adj.homEquiv X Y).bijective

/-- Any morphism `r : plist A P ⟶ Y` which composes with `plist.nil` to `init` and
composes with `plist.cons` to `A ◁ r ≫ action` is equal to `plist.rc init action`. -/
theorem rc_uniq {A P Y : C} {init : P ⟶ Y} {action : A ⊗ Y ⟶ Y}
    (r : plist A P ⟶ Y) (h_nil : nil ≫ r = init) (h_cons : cons ≫ r = A ◁ r ≫ action) :
    r = rc init action := by
  let adj := freeForgetAdj A
  let rAlgHom : (freeActionFunctor A).obj P ⟶ ⟨Y, action⟩ := ⟨r, h_cons.symm⟩
  let rcAlgHom : (freeActionFunctor A).obj P ⟶ ⟨Y, action⟩ := ⟨rc init action, plist.cons_rc.symm⟩
  have r_tr_eq_rc_tr : adj.homEquiv P ⟨Y, action⟩ rAlgHom = adj.homEquiv P ⟨Y, action⟩ rcAlgHom := by
    rwa [← nil_rc (init:= init) (action:= action)] at h_nil
  injection adj.homEquiv .. |>.bijective.1 r_tr_eq_rc_tr

/-- If two morphisms `f, g : plist A P ⟶ Y` agree on `nil` and `cons`, then they are equal. -/
theorem ext {A P Y : C} {f g : plist A P ⟶ Y} (h₀ : nil ≫ f = nil ≫ g)
  (h₁ : cons ≫ f = cons ≫ g)  : f = g := sorry

theorem rc_nil_cons_id : rc nil cons = 𝟙 (plist A P) := by
  rw [← rc_uniq]
  · simp only [comp_id, whiskerLeft_id, id_comp, rc_uniq, nil_rc]
  · simp only [comp_id, whiskerLeft_id, id_comp, rc_uniq, nil_rc]

theorem map'_eq_rc {A P P' : C} {f : P ⟶ P'} :
    (plist.map' A f) = plist.rc (f ≫ plist.nil) plist.cons := by
  refine rc_uniq (Act.forget.map (freeActionFunctor A |>.map f)) ?_ ?_
  · simp only [nil, Adjunction.unit_naturality]
  · simp only [cons, Act.forget, forget_map, Act.hom]

@[simp]
theorem map'_id (A : C) : plist.map' A (𝟙 _) = 𝟙 (plist A (𝟙_ C)) := by {
  dsimp [plist.map']
  simp only [Functor.map_id, comp_id, whiskerLeft_id, id_comp,
    plist.rc_uniq, plist.nil_rc]
  exact rfl}

/-- Covariant action of `plist` on morphisms of the first argument.
A morphism `f : A ⟶ B` induces a morphism `plist.map f : plist A P ⟶ plist B P`. -/
def map {B : C} (f : A ⟶ B) : plist A P ⟶ plist B P := rc nil (f ▷ (plist B P) ≫ cons)

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
theorem nil_map {B: C} {f : A ⟶ B} : (nil : P ⟶ plist A P) ≫ map f = nil := by
  simp only [map, nil_rc]

@[simp]
theorem cons_map {B : C} {f : A ⟶ B} :
    (cons : A ⊗ plist A P ⟶ plist A P) ≫ map f =
    (A ◁ map f) ≫ (f ▷ plist B P) ≫ cons := by
  simp only [map, cons_rc]

@[reassoc (attr := simp)]
theorem whiskerLeft_nil_whiskerLeft_map {B : C} {f : A ⟶ B} :
    (A ◁ plist.nil) ≫ (A ◁ plist.map f (P := P)) = A ◁ plist.nil := by
  rw [← whiskerLeft_comp, nil_map]

@[reassoc (attr := simp)]
theorem whiskerRight_nil_whiskerRight_map {B : C} {f : A ⟶ B} :
    (plist.nil ▷ P) ≫ (plist.map f (P := P) ▷ P) = (plist.nil ▷ P) := by
  rw [← comp_whiskerRight, nil_map]

@[simp]
theorem map_id : map (𝟙 A) = 𝟙 (plist A P) := by
   dsimp [map]
   simp only [id_whiskerRight, id_comp, nil_rc, comp_id, whiskerLeft_id, rc_uniq]
   exact rc_nil_cons_id

@[simp]
theorem map_comp {A B B' P : C} (f : A ⟶ B) (g : B ⟶ B') :
    plist.map (P := P) (f ≫ g) = plist.map f ≫ plist.map g := by
  dsimp [map]
  rw [← rc_uniq]
  · rw [← assoc, nil_rc]
    rw [nil_rc]
  · rw [← assoc, cons_rc]
    simp only [assoc,whiskerLeft_comp, comp_whiskerRight]
    rw [← assoc, cons_rc]
    rw [assoc]
    refine A ◁ rc nil (f ▷ plist B P ≫ cons) ≫= ?_
    exact
      Eq.symm (whisker_exchange_assoc f (rc nil (g ▷ plist B' P ≫ cons)) (g ▷ plist B' P ≫ cons))

variable (P)

def functor : C ⥤ C where
  obj A := plist A P
  map := plist.map
  map_id _ := plist.map_id
  map_comp := plist.map_comp

open Category

variable (A)

/-- The comparision morphism `plist A (P ⊗ X) ⟶ (plist A P) ⊗ X`. -/
def cmp (X : C) : plist A (P ⊗ X) ⟶ (plist A P) ⊗ X :=
  plist.rc (plist.nil ▷ X) ((α_ _ _ _).inv ≫ (plist.cons ▷ X))

variable {A P}

@[reassoc (attr := simp)]
theorem nil_cmp {X : C} : plist.nil ≫ plist.cmp A P X = plist.nil ▷ X := by
  simp [cmp]

@[reassoc (attr := simp)]
theorem cons_cmp {X : C} :
    plist.cons ≫ plist.cmp .. = (A ◁ plist.cmp A P X) ≫ ((α_ _ _ _).inv ≫ (plist.cons ▷ X)) := by
  simp [cmp, plist.cons_rc]

end plist

/-- The list object defined as the recursive object
  with the terminal object as paramter `P`. -/
def list [MonoidalCategory C] [Recursive C] (A : C) : C := plist A (𝟙_ C)

namespace list

variable [MonoidalCategory C] [Recursive C] {A : C}

/- ε : 1 ⟶ list A -/
def nil : 𝟙_ C ⟶ list A := plist.nil (P := 𝟙_ C)

/- cons : A × list A ⟶ list A -/
def cons : A ⊗ list A ⟶ list A := plist.cons (P := 𝟙_ C)

/-- The weak non-parametized recursion scheme for the list object. See `list.prc` for the
parameterized version. -/
def rc {Y : C} (init : 𝟙_ C ⟶ Y) (action : A ⊗ Y ⟶ Y) : list A ⟶ Y := plist.rc init action

-- [a, b, c].foldr f init  = f a (f b (f c init))
def foldr {Y : C} (f : A ⊗ Y ⟶ Y) (e : 𝟙_ C ⟶ Y) : list A ⟶ Y := plist.rc e f

-- SH: I don't think this is foldl. It gives
-- [a, b, c].foldl f init  = f (f (f init c) b) a`
-- while it should be f (f (f init a) b) c
def foldl [BraidedCategory C] {Y : C} (f : Y ⊗ A ⟶ Y) (e : 𝟙_ C ⟶ Y) : list A ⟶ Y :=
  plist.rc e ((β_ A Y).hom ≫ f)

def map {B : C} (f : A ⟶ B) : list A ⟶ list B := plist.map (P := 𝟙_ C) f

@[reassoc (attr := simp)]
theorem map_nil {B : C} {f : A ⟶ B} :
    (list.nil : 𝟙_ C ⟶ list A) ≫ list.map f = plist.nil := by
  simp only [list.nil, list.map, plist.nil_map]

@[simp]
theorem cons_map {B : C} {f : A ⟶ B} :
    cons ≫ map f = (A ◁ map f) ≫ (f ▷ list B) ≫ cons := by
  simp only [list, list.cons, list.map, plist.cons_map]

@[simp]
theorem map_comp {B B' : C} (f : A ⟶ B) (g : B ⟶ B') :
    map (f ≫ g) = map f ≫ map g := by
  simp only [list.map, plist.map_comp]

@[simp]
theorem map_id : list.map (𝟙 A) = 𝟙 (list A) := by
  simp only [list.map, plist.map_id, list]

def singleton : A ⟶ list A :=
  (ρ_ A).inv ≫ (A ◁ (list.nil)) ≫ list.cons

/- [x] as x :: [] -/
theorem singleton_eq_nil_cons : singleton = (ρ_ A).inv ≫ (A ◁ list.nil) ≫ list.cons := by
  dsimp [list.singleton, list.cons, list.nil]

end list

variable (C)

-- open Recursive

-- class ListArithmetic' where
--   is_iso {A P Y : C} : IsIso (plist.cmp A P Y)

/-- A recursive category is list-arithmetic if the comparison morphisms `cmp A P Y` are
all isomorphisms. -/
class ListArithmetic [MonoidalCategory C] extends Recursive C where
  cmpInv (A P Y : C) : plist A P ⊗ Y ⟶ plist A (P ⊗ Y)
  hom_inv_id {A P Y} : plist.cmp A P Y ≫ cmpInv A P Y = 𝟙 _
  inv_hom_id {A P Y} : cmpInv A P Y ≫ plist.cmp A P Y = 𝟙 _

section ListArithmetic

open ListArithmetic

variable {C} [MonoidalCategory C] [ListArithmetic C]

instance plist.cmp.is_iso {A P Y : C} : IsIso (plist.cmp A P Y) := by
  use cmpInv A P Y
  constructor
  rw [ListArithmetic.hom_inv_id]
  rw [ListArithmetic.inv_hom_id]

/-- In a list-arithmetic category, `plist A P` is isomorphic to `(list A) ⊗ P`. -/
def plistIsoTensor (A P : C) : plist A P ≅ list A ⊗ P where
  hom := plist.map' A (λ_ P).inv ≫ plist.cmp A (𝟙_ C) P
  inv := cmpInv A (𝟙_ C) P ≫ ((plist.map' A (λ_ P).hom))
  hom_inv_id := by
    refine (hom_comp_eq_id (plist.map' A (λ_ P).inv ≫ plist.cmp A (𝟙_ C) P)).mpr ?_
    have := ListArithmetic.inv_hom_id (A:= A) (P:= (𝟙_ C)) (Y:= P)
    simp only [IsIso.inv_comp, IsIso.eq_comp_inv, assoc]
    refine Eq.symm (IsIso.inv_eq_of_inv_hom_id ?_)
    rw [← this]
    rw [assoc]
    rw [assoc]
    refine cmpInv A (𝟙_ C) P ≫= ?_
    rw [← assoc]
    rw [← plist.map'_comp]
    simp only [Iso.hom_inv_id]
    rw [plist.map'_id_tensor]
    simp only [comp_id, whiskerLeft_id, id_comp, plist.rc_uniq, plist.nil_rc]
  inv_hom_id := by
    refine (comp_hom_eq_id (plist.map' A (λ_ P).inv ≫ plist.cmp A (𝟙_ C) P)).mpr ?_
    have := ListArithmetic.hom_inv_id (A:= A) (P:= (𝟙_ C)) (Y:= P)
    simp only [IsIso.inv_comp, IsIso.eq_comp_inv, assoc]
    refine Eq.symm (IsIso.inv_eq_of_hom_inv_id ?_)
    rw [← this]
    rw [← plist.map'_comp]
    simp only [Iso.hom_inv_id, plist.map'_id_tensor, comp_id, whiskerLeft_id, id_comp,
      plist.rc_uniq, plist.nil_rc]

/-- Paramterized recursion scheme for the list object in a list-arithmetic category. -/
def list.prc {A P Y : C} (e : P ⟶ Y) (a : A ⊗ Y ⟶ Y) : list A ⊗ P ⟶ Y :=
  (plistIsoTensor A P).inv ≫ plist.rc e a

theorem list.prc_rc {A Y : C} (e : 𝟙_ C ⟶ Y) (a : A ⊗ Y ⟶ Y) :
    (ρ_ (list A)).inv ≫ list.prc e a = list.rc e a := by
  sorry

namespace list

local notation "η" => list.singleton

/--
```
     nil⊗P              prc
1 ⊗ P ----> list A ⊗ P -----> Y
  |            |              |
≅ |            | ≅            |
  |            |              |
  P  -----> plist A P  ---->  Y
      nil               rc
```
-/
@[reassoc (attr := simp)]
theorem nil_prc {A P Y : C} {init : P ⟶ Y} {action : A ⊗ Y ⟶ Y} :
    (list.nil ▷ P) ≫ list.prc init action = (λ_ P).hom ≫ init := by
  dsimp [prc]
  nth_rw 2 [← plist.nil_rc (init := init) (action := action)]
  rw [← assoc]
  rw [← assoc]
  refine ?_ =≫ plist.rc init action
  refine (Iso.comp_inv_eq (plistIsoTensor A P)).mpr ?_
  simp only [assoc]
  dsimp [list.nil, plistIsoTensor]
  rw [plist.map'_eq_rc]
  dsimp [plist.cmp]
  simp only [plist.nil_rc, plist.nil_rc_assoc, assoc, Iso.hom_inv_id_assoc]

theorem cons_prc {A P Y : C} {init : P ⟶ Y} {action : A ⊗ Y ⟶ Y} :
    (list.cons ▷ P) ≫ list.prc init action = (α_ _ _ _).hom ≫ (A ◁ list.prc init action) ≫ action := by
  dsimp [prc,cons]
  sorry

@[simp]
theorem prc_uniq {A P Y : C} {init : P ⟶ Y} {action : A ⊗ Y ⟶ Y}
    (r : list A ⊗ P ⟶ Y) (h_nil : nil ▷ P ≫ r = (λ_ _).hom ≫ init)
    (h_cons : cons ▷ P ≫ r = (α_ _ _ _).hom ≫ (A ◁ r) ≫ action) :
    r = prc init action := by
  simp [nil, cons] at *
  refine (Iso.eq_inv_comp (plistIsoTensor A P)).mpr ?_
  rw [plist.rc_uniq (r:= (plistIsoTensor A P).hom ≫ r)]
  · dsimp [plistIsoTensor]
    rw [← assoc,← assoc, plist.map'_eq_rc]
    simp only [plist.nil_rc, assoc, plist.nil_cmp]
    rw [h_nil]
    simp only [Iso.inv_hom_id_assoc]
  · simp only [whiskerLeft_comp, assoc]
    dsimp [plistIsoTensor]
    rw [plist.map'_eq_rc]
    rw [← assoc, ← assoc, plist.cons_rc]
    simp only [assoc, plist.cons_cmp, whiskerLeft_comp]
    rw [h_cons]
    dsimp [list]
    simp only [Iso.inv_hom_id_assoc]

def pfoldr {A P Y : C} (a : A ⊗ Y ⟶ Y) (e : P ⟶ Y) : list A ⊗ P ⟶ Y := list.prc e a

/-- Appends two lists. -/
def append {A : C} : list A ⊗ list A ⟶ list A := list.prc (𝟙 _) (list.cons)

-- [] ++ xs = xs
@[reassoc (attr := simp)]
theorem whiskerRight_nil_append {A : C} : list.nil ▷ list A ≫ append = (λ_ (list A)).hom := by
  simp [append]

--xs ++ [] = xs
theorem whiskerLeft_nil_append {A : C} : list A ◁ list.nil ≫ append = (ρ_ (list A)).hom := by
  sorry

-- (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
theorem append_assoc {A : C} :
    append ▷ list A ≫ append = (α_ _ _ _).hom ≫ (list A ◁ append) ≫ append := by
  sorry

-- map f (xs ++ ys) = map f xs ++ map f ys
theorem append_map {A B : C} {f : A ⟶ B} :
    append ≫ list.map f = ((list.map f) ⊗ₘ (list.map f)) ≫ append := by
  sorry

-- ⁠[x] ++ xs = x :: xs
theorem singleton_append_eq_cons [BraidedCategory C] {A : C} :
    (η ▷ list A) ≫ list.append = list.cons := by
  dsimp [append,list.singleton]
  simp only [comp_whiskerRight, whisker_assoc, assoc, triangle_assoc_comp_right_inv_assoc]
  rw [cons_prc]
  have : A ◁ (λ_ (list A)).inv ≫
    A ◁ nil ▷ list A ≫ (α_ A (list A) (list A)).inv ≫
    (α_ A (list A) (list A)).hom ≫ A ◁ prc (𝟙 (list A)) cons ≫ cons=
    A ◁ (λ_ (list A)).inv ≫
    (A ◁ nil ▷ list A ≫ (α_ A (list A) (list A)).inv ≫
     (α_ A (list A) (list A)).hom ≫ A ◁ prc (𝟙 (list A)) cons) ≫ cons :=
       by {simp only [Iso.inv_hom_id_assoc, assoc]}
  rw [this]
  clear this
  refine (IsIso.eq_inv_comp (A ◁ (λ_ (list A)).inv)).mp ?_
  refine ?_ =≫ cons
  simp only [Iso.inv_hom_id_assoc, inv_whiskerLeft, IsIso.Iso.inv_inv]
  refine (inv_comp_eq_id (A ◁ (λ_ (plist A (𝟙_ C))).hom)).mp ?_
  simp only [inv_whiskerLeft, IsIso.Iso.inv_hom]
  have {A P Y : C} {init : P ⟶ Y} {action : A ⊗ Y ⟶ Y} :
     nil ▷ P ≫ prc init action = (λ_ P).hom ≫ init := nil_prc
  rw [← whiskerLeft_comp]
  rw [nil_prc]
  dsimp [list]
  simp only [comp_id, whiskerLeft_id, id_comp, plist.rc_uniq,
    plist.nil_rc, whiskerLeft_inv_hom]

def snoc {A : C} : list A ⊗ A ⟶ list A := (list A ◁ singleton) ≫ append

theorem braiding_hom_list_unit_twist [BraidedCategory C] {P : C} :
    (β_ (list (𝟙_ C)) P).hom = list.prc ((ρ_ P).inv ≫ P ◁ (list.nil (A:= 𝟙_C))) (λ_ _).hom := by
  sorry

/-- Reverses a list, i.e. the list with the elements in reverse order. -/
def rev [BraidedCategory C] {A : C} : list A ⟶ list A :=
  list.rc list.nil ((η ▷ list A) ≫ (β_ _ _).hom ≫ append)

/- rev_nil [] = [] -/
theorem nil_rev [BraidedCategory C] {A : C} : list.nil ≫ rev = list.nil (A := A) := by
  dsimp [rev, list.nil, list.rc]
  simp only [plist.nil_rc]

/- rev [x] = [x] -/
theorem singleton_rev_eq_singleton [BraidedCategory C] {A : C} : η ≫ rev (A := A) = η := by
  simp only [rev, list.singleton]
  sorry

/- rev (xs ++ ys) = rev ys ++ rev xs -/
theorem rev_append [BraidedCategory C] {A : C} :
    append ≫ rev (A:= A) = (rev ⊗ₘ rev) ≫ list.append := by
  sorry

/- rev (rev xs ++ [x]) = [x] ++ xs -/
theorem singleton_braiding_append_rev_eq_singleton_append [BraidedCategory C] {A : C} :
    ((η ▷ list A) ≫ (β_ _ _).hom ≫ list.append ≫ list.rev) =
    (η ▷ list A) ≫ list.append  := by
  sorry

/-- list.rev is an involution, i.e. `list.rev ≫ list.rev = 𝟙`. -/
theorem rev_rev [BraidedCategory C] {A : C} : list.rev ≫ list.rev = 𝟙 (list A) :=
  sorry

/-- Concatenates a list of lists into a single list, preserving the order of the elements. -/
def flatten {A : C} : list (list A) ⟶ list A := list.rc list.nil list.append

end list

@[simps]
def List.freeActionFunctor (A : Type u) : Type u ⥤ Act A where
  obj P := ⟨List A × P, fun ⟨a,as,p⟩ => ⟨(a::as),p⟩⟩
  map f := ⟨fun a => (a.1, f a.2), _⟩

def ListAdjActForgetHomEquiv (A P : Type u₁) (Y : Act A) :
    ((List.freeActionFunctor A).obj P ⟶ Y) ≃ (P ⟶ Act.forget.obj Y) where
  toFun f := fun p => f.1 ([], p)
  invFun f := ⟨fun x => x.1.foldr (fun a b => Y.str (a, b)) (f x.2), rfl⟩
  left_inv f := by
    ext x
    rcases x with ⟨as, p⟩
    revert p
    induction as with
    | nil =>
        intro p
        simp [List.foldr]
    | cons a as ih =>
        intro p
        have h := congrArg (fun (g : (A × (List A × P)) → _) => g (a, (as, p))) f.h
        simp only [List.foldr_cons]
        simp_all only [List.freeActionFunctor_obj_a, curriedTensor_obj_obj, curriedTensor_obj_map, types_comp_apply,
          whiskerLeft_apply, List.freeActionFunctor_obj_str]
  right_inv f := by
    funext x
    rfl

instance : Recursive (Type u) where
  withRec A := {
    freeActionFunctor := List.freeActionFunctor A
    freeForgetAdj := Adjunction.mkOfHomEquiv {
      homEquiv := ListAdjActForgetHomEquiv A
      homEquiv_naturality_left_symm := by {
        intros X' X Y f g
        dsimp [ListAdjActForgetHomEquiv]
        dsimp [List.freeActionFunctor]
        ext a
        simp only [comp_f, types_comp_apply]
      }
      homEquiv_naturality_right :=  fun {X} {Y Y'} f g ↦ rfl
      }
    }

/-- The category of types is list-arithmetic. -/
instance : ListArithmetic (Type u) where
  cmpInv A P Y := fun ⟨⟨l, p⟩, y⟩ => ⟨l, ⟨p, y⟩⟩
  hom_inv_id := by
    intro A P Y
    have cmp_computes : ∀ (l : List A) (p : P) (y : Y),
        plist.cmp A P Y (l, (p, y)) = ((l, p), y) := by
      intro l; revert l; intro l p y; revert p y
      induction l with
      | nil =>
        intro p y
        rfl
      | cons a as ih =>
        intro p y
        let d : A × (List A × (P × Y)) := (a, (as, (p, y)))
        have : (plist.cons ≫ plist.cmp A P Y) d =
         (A ◁ plist.cmp A P Y ≫ (α_ A (plist A P) Y).inv ≫ plist.cons ▷ Y) d := rfl
        simp only [types_comp_apply, whiskerLeft_apply, whiskerRight_apply,
          associator_inv_apply_2] at this
        have cons_eq : (a :: as, (p, y)) = ((List.freeActionFunctor A).obj (P × Y)).str d := rfl
        dsimp [plist.cons] at this
        rw [cons_eq]
        simp_all only [associator_inv_apply, List.freeActionFunctor_obj_str, d]
        exact this
    funext ⟨l, p, y⟩
    simp only [types_comp_apply, types_id_apply]
    rw [cmp_computes]
  inv_hom_id := by
    intro A P Y
    have cmp_computes : ∀ (l : List A) (p : P) (y : Y),
        plist.cmp A P Y (l, (p, y)) = ((l, p), y) := by
      intro l; revert l; intro l p y; revert p y
      induction l with
      | nil =>
        intro p y
        rfl
      | cons a as ih =>
        intro p y
        let d : A × (List A × (P × Y)) := (a, (as, (p, y)))
        have : (plist.cons ≫ plist.cmp A P Y) d =
         (A ◁ plist.cmp A P Y ≫ (α_ A (plist A P) Y).inv ≫ plist.cons ▷ Y) d := rfl
        simp only [types_comp_apply, whiskerLeft_apply, whiskerRight_apply,
          associator_inv_apply_2] at this
        have cons_eq : (a :: as, (p, y)) = ((List.freeActionFunctor A).obj (P × Y)).str d := rfl
        dsimp [plist.cons] at this
        rw [cons_eq]
        simp_all only [associator_inv_apply, List.freeActionFunctor_obj_str, d]
        exact this
    funext ⟨⟨l, p⟩, y⟩
    simp only [types_comp_apply, types_id_apply]
    exact cmp_computes l p y

end ListArithmetic

variable {C}

class Semirecursive [MonoidalCategory C] [HasBinaryCoproducts C] (A P L : C) where
  nil : P ⟶ L -- nil
  cons : A ⊗ L  ⟶ L -- cons
  split : L ⟶ P ⨿ A ⊗ L -- split
  nil_split : nil ≫ split = coprod.inl
  cons_split : cons ≫ split = coprod.inr
  split_nil_cons : split ≫ (coprod.desc nil cons) = 𝟙 L -- split is a section of the coprod.desc

/-- split is an isomorphism in a semirecursive category. -/
instance [MonoidalCategory C] [HasBinaryCoproducts C] {A P L : C} [Semirecursive A P L]  :
    IsIso (Semirecursive.split : L ⟶ P ⨿ A ⊗ L) := by
  constructor
  use coprod.desc (Semirecursive.nil A) (Semirecursive.cons P)
  constructor
  · exact Semirecursive.split_nil_cons
  · refine coprod.hom_ext ?_ ?_
    · simp only [coprod.desc_comp, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.ι_app_left,
      BinaryCofan.mk_inl, comp_id]
      exact Semirecursive.nil_split
    · simp only [coprod.desc_comp, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.ι_app_right,
      BinaryCofan.mk_inr, comp_id]
      exact Semirecursive.cons_split

noncomputable instance list.semirecursive [MonoidalCategory C] [HasBinaryCoproducts C] [ListArithmetic C] {A : C}:
    Semirecursive A (𝟙_ C) (list A) where
  nil := list.nil
  cons := list.cons
  split := by {
    dsimp [list]
    refine plist.rc ?_ ?_
    · exact coprod.inl
    · have i₂ := coprod.inr (X := 𝟙_ C) (Y := A ⊗ plist A (𝟙_ C))
      have Axecons : A ⊗ (𝟙_ C ⨿ A ⊗ plist A (𝟙_ C)) ⟶ A ⊗ plist A (𝟙_ C) :=
        𝟙 A ⊗ₘ coprod.desc plist.nil plist.cons
      exact Axecons ≫ i₂
    }
  nil_split := plist.nil_rc
  cons_split := by {
    dsimp
    let Axecons : A ⊗ (𝟙_ C ⨿ A ⊗ plist A (𝟙_ C)) ⟶ A ⊗ plist A (𝟙_ C) :=
        𝟙 A ⊗ₘ coprod.desc plist.nil plist.cons
    let i₂ := coprod.inr (X := 𝟙_ C) (Y := A ⊗ plist A (𝟙_ C))
    let f := plist.rc coprod.inl (Axecons ≫ i₂)
    let econs : (𝟙_ C ⨿ A ⊗ plist A (𝟙_ C)) ⟶ plist A (𝟙_ C) :=
     coprod.desc plist.nil plist.cons
    let i₁ := coprod.inl (X := 𝟙_ C) (Y := A ⊗ plist A (𝟙_ C))
    let i₁focons := coprod.desc i₁ (cons ≫ f)
    let Axf : A ⊗ list A ⟶ A ⊗ (𝟙_ C ⨿ A ⊗ plist A (𝟙_ C)) := 𝟙 A ⊗ₘ f
    have : f ≫ econs = 𝟙 (list A) := by {
      dsimp [list]
      rw [← plist.rc_nil_cons_id]
      rw [← plist.rc_uniq]
      · dsimp [f, econs]
        simp only [plist.nil_rc_assoc]
        simp only [colimit.ι_desc, BinaryCofan.mk_pt,
          BinaryCofan.ι_app_left, BinaryCofan.mk_inl]
      · rw [← assoc]
        dsimp [f, econs, Axecons, i₂]
        rw [plist.cons_rc]
        simp only [assoc, whiskerLeft_comp]
        simp only [id_tensorHom]
        simp only [colimit.ι_desc, BinaryCofan.mk_pt,
          BinaryCofan.ι_app_right, BinaryCofan.mk_inr]
    }
    have topSqComm : cons ≫ f = Axf ≫ Axecons ≫ i₂ := by {
      dsimp [f, Axf, Axecons, i₂,list.cons]
      simp only [id_tensorHom]
      rw [plist.cons_rc]
    }
    change cons ≫ f = coprod.inr (C:=C)
    rw [topSqComm]
    dsimp [Axf,Axecons]
    dsimp [econs] at this
    dsimp [i₂]
    rw [← assoc]
    nth_rw 2 [← id_comp (f := coprod.inr)]
    have hthis :
    ((𝟙 A ⊗ₘ f ≫ coprod.desc plist.nil plist.cons)) =
     ((𝟙 A ⊗ₘ f) ≫ (𝟙 A ⊗ₘ coprod.desc plist.nil plist.cons)) := by {
      simp only [id_tensorHom, whiskerLeft_comp]
     }
    rw [← hthis, this]
    simp only [id_tensorHom, id_comp]
    exact whiskerLeft_id_assoc A (plist A (𝟙_ C)) coprod.inr
  }
  split_nil_cons := by {
    let i₂ := coprod.inr (X := 𝟙_ C) (Y := A ⊗ plist A (𝟙_ C))
    let i₁ := coprod.inl (X := 𝟙_ C) (Y := A ⊗ plist A (𝟙_ C))
    let econs : (𝟙_ C ⨿ A ⊗ plist A (𝟙_ C)) ⟶ plist A (𝟙_ C) :=
     coprod.desc plist.nil plist.cons
    let Axecons := 𝟙 A ⊗ₘ econs
    let f := plist.rc coprod.inl (Axecons ≫ i₂)
    change f ≫ econs = 𝟙 (list A)
    let Axf : A ⊗ list A ⟶ A ⊗ (𝟙_ C ⨿ A ⊗ plist A (𝟙_ C)) := 𝟙 A ⊗ₘ f
    dsimp [list]
    rw [← plist.rc_nil_cons_id]
    rw [← plist.rc_uniq]
    · dsimp [f, econs]
      simp only [plist.nil_rc_assoc]
      simp only [colimit.ι_desc, BinaryCofan.mk_pt,
        BinaryCofan.ι_app_left, BinaryCofan.mk_inl]
    · rw [← assoc]
      dsimp [f]
      rw [plist.cons_rc]
      dsimp [econs, Axecons, econs, i₂]
      simp only [assoc, whiskerLeft_comp]
      simp only [id_tensorHom]
      simp only [colimit.ι_desc, BinaryCofan.mk_pt,
        BinaryCofan.ι_app_right, BinaryCofan.mk_inr]
    }

noncomputable instance plist.semirecursive [MonoidalCategory C] [HasBinaryCoproducts C]
    [ListArithmetic C] {A P : C} :
    Semirecursive A P (plist A P) where
  nil := plist.nil
  cons := plist.cons
  split := by {
    apply plist.rc coprod.inl
    · exact (𝟙 A ⊗ₘ coprod.desc plist.nil plist.cons) ≫
         (coprod.inr (X := P) (Y := A ⊗ plist A P))}
  nil_split := by {
    simp only [id_tensorHom, nil_rc]
  }
  cons_split := by {
    let Axecons : A ⊗ (P ⨿ A ⊗ plist A P) ⟶ A ⊗ plist A P :=
        𝟙 A ⊗ₘ coprod.desc plist.nil plist.cons
    let i₂ := coprod.inr (X := P) (Y := A ⊗ plist A P)
    let f := plist.rc coprod.inl (Axecons ≫ i₂)
    let econs : (P ⨿ A ⊗ plist A P) ⟶ plist A P :=
     coprod.desc plist.nil plist.cons
    let i₁ := coprod.inl (X := P) (Y := A ⊗ plist A P)
    let i₁focons := coprod.desc i₁ (cons ≫ f)
    let Axf : A ⊗ plist A P ⟶ A ⊗ (P ⨿ A ⊗ plist A P) := 𝟙 A ⊗ₘ f
    have : f ≫ econs = 𝟙 (plist A P) := by {
      rw [← plist.rc_nil_cons_id, ← plist.rc_uniq]
      · dsimp [f, econs]
        simp only [plist.nil_rc_assoc]
        simp only [colimit.ι_desc, BinaryCofan.mk_pt,
          BinaryCofan.ι_app_left, BinaryCofan.mk_inl]
      · rw [← assoc]
        dsimp [f, econs, Axecons, i₂]
        rw [plist.cons_rc]
        simp only [assoc, whiskerLeft_comp]
        simp only [id_tensorHom]
        simp only [colimit.ι_desc, BinaryCofan.mk_pt,
          BinaryCofan.ι_app_right, BinaryCofan.mk_inr]
    }
    have topSqComm : cons ≫ f = Axf ≫ Axecons ≫ i₂ := by {
      dsimp [f, Axf, Axecons, i₂, list.cons]
      simp only [id_tensorHom]
      rw [plist.cons_rc]
    }
    change cons ≫ f = coprod.inr (C:=C)
    rw [topSqComm]
    dsimp [Axf,Axecons]
    dsimp [econs] at this
    dsimp [i₂]
    rw [← assoc]
    nth_rw 2 [← id_comp (f := coprod.inr)]
    have hthis :
    ((𝟙 A ⊗ₘ f ≫ coprod.desc plist.nil plist.cons)) =
     ((𝟙 A ⊗ₘ f) ≫ (𝟙 A ⊗ₘ coprod.desc plist.nil plist.cons)) := by {
      simp only [id_tensorHom, whiskerLeft_comp]
     }
    rw [← hthis,this]
    simp only [id_tensorHom, id_comp]
    exact whiskerLeft_id_assoc A (plist A P) coprod.inr
  }
  split_nil_cons := by {
    let i₂ := coprod.inr (X := P) (Y := A ⊗ plist A P)
    let i₁ := coprod.inl (X := P) (Y := A ⊗ plist A P)
    let econs : (P ⨿ A ⊗ plist A P) ⟶ plist A (P) :=
     coprod.desc plist.nil plist.cons
    let Axecons := 𝟙 A ⊗ₘ econs
    let f := plist.rc coprod.inl (Axecons ≫ i₂)
    change f ≫ econs = 𝟙 (plist A P)
    let Axf : A ⊗ plist A P ⟶ A ⊗ (P ⨿ A ⊗ plist A P) := 𝟙 A ⊗ₘ f
    rw [← plist.rc_nil_cons_id, ← plist.rc_uniq]
    · dsimp [f, econs]
      simp only [plist.nil_rc_assoc]
      simp only [colimit.ι_desc, BinaryCofan.mk_pt,
        BinaryCofan.ι_app_left, BinaryCofan.mk_inl]
    · rw [← assoc]
      dsimp [f, econs, Axecons, econs, i₂]
      rw [plist.cons_rc]
      simp only [assoc, whiskerLeft_comp]
      simp only [id_tensorHom]
      simp only [colimit.ι_desc, BinaryCofan.mk_pt,
        BinaryCofan.ι_app_right, BinaryCofan.mk_inr]}

section Tail

variable [SemiCartesianMonoidalCategory C] [HasBinaryCoproducts C] [ListArithmetic C]

open SemiCartesianMonoidalCategory

noncomputable def list.tail {A : C} : list A ⟶ 𝟙_ C ⨿ list A :=
  list.semirecursive.split (A:= A) (L:= list A) ≫ (coprod.map (𝟙 _) (snd A (list A)))

noncomputable def list.head {A : C} : list A ⟶ 𝟙_ C ⨿ A :=
  list.semirecursive.split (A:= A) (L:= list A) ≫ (coprod.map (𝟙 _) (fst A (list A)))

theorem list.nil_tail {A : C} : list.nil ≫ list.tail (A:= A) = coprod.inl := by
  dsimp [tail,Semirecursive.split]
  rw [← assoc]
  dsimp [list.nil]
  simp only [id_tensorHom, plist.nil_rc, coprod.inl_map, id_comp]

theorem list.cons_tail {A : C} : list.cons ≫ list.tail (A:= A) = snd _ _ ≫ coprod.inr := by
  sorry

theorem list.singleton_tail {A : C} :
    list.singleton ≫ list.tail (A:= A) = toUnit A ≫ list.nil ≫ coprod.inr := by
  sorry

/-- The object of nonempty lists. -/
noncomputable def nelist [HasPullbacks C] (A : C) := pullback (list.tail (A:= A)) coprod.inr

noncomputable def nelistToList [HasPullbacks C] (A : C) : nelist A ⟶ list A :=
  pullback.snd _ _

theorem isMono_nelistToList [HasPullbacks C] (A : C) : Mono (nelistToList A) := by
  sorry

end Tail

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

section listAsEndofunctorAlgebra

variable [MonoidalCategory C] [HasBinaryCoproducts C]

/-- The endofunctor `X ↦ P ⨿ (A ⊗ X)` on the category `C`. -/
noncomputable def coprodTensorEndofunctor (A P : C) : C ⥤ C where
  obj X := P ⨿ (A ⊗ X)
  map {X Y} f := coprod.map (𝟙 _) (A ◁ f)

/-- The algebra associated to a pair `init : P ⟶ X` and `action A ⊗ X ⟶ X` of morphisms for the endofunctor `X ↦ P ⨿ (A ⊗ X)`. -/
noncomputable def coprodTensorEndofunctorAlgebraMk {A P} (X : C) (init : P ⟶ X) (action : A ⊗ X ⟶ X) :
    Algebra (coprodTensorEndofunctor A P) := ⟨X, coprod.desc init action⟩

/-- The init morphism `P ⟶ α.a` for an algebra of the endofunctor `X ↦ P ⨿ (A ⊗ X)`. -/
noncomputable def initOfCoprodTensorEndofunctorAlgebra {A P : C} (α : Algebra (coprodTensorEndofunctor A P)) :
    P ⟶ α.a := coprod.inl ≫ α.str

/-- The action morphism `A ⊗ α.a ⟶ α.a` for an algebra of the endofunctor `X ↦ P ⨿ (A ⊗ X)`. -/
noncomputable def actionOfcoprodTensorEndofunctorAlgebra {A P : C} (α : Algebra (coprodTensorEndofunctor A P)) :
    A ⊗ α.a ⟶ α.a := coprod.inr ≫ α.str

/-- The algebra associated to the parameterized list object `plist A P` for the endofunctor `X ↦ P ⨿ (A ⊗ X)`. -/
noncomputable def plistAlgebra [ListArithmetic C] (A P : C) :
    Algebra (coprodTensorEndofunctor A P) :=
  coprodTensorEndofunctorAlgebraMk (plist A P) plist.nil plist.cons

theorem plistAlgebra_a [ListArithmetic C] {A P : C} : (plistAlgebra A P).a = plist A P := by
  rfl

theorem plistAlgebra_str [ListArithmetic C] {A P : C} :
    (plistAlgebra A P).str = coprod.desc plist.nil plist.cons := by
  rfl

/-- The algebra associated to the list object `list A` for the endofunctor `X ↦ 1 ⨿ (A ⊗ X)`. -/
noncomputable def listAlgebra [ListArithmetic C] (A : C) := plistAlgebra A (𝟙_ C)

theorem listAlgebra_a [ListArithmetic C] {A : C} : (listAlgebra A).a = list A := by
  rfl

theorem listAlgebra_str [ListArithmetic C] {A : C} :
    (listAlgebra A).str = coprod.desc list.nil list.cons := by
  rfl

/-- In a list-arithmetic category, the parametrize list object is the initial algebra for the polynomial endofunctor `X ↦ P ⨿ A ⊗ X`. -/
noncomputable instance isInitialOfplistAlgebra [ListArithmetic C] (A P : C)  :
    IsInitial (plistAlgebra A P) := by
  refine IsInitial.ofUniqueHom  (fun α => ?_) ?uniq
  · exact {
    f := plist.rc (initOfCoprodTensorEndofunctorAlgebra α) (actionOfcoprodTensorEndofunctorAlgebra α)
    h := by sorry
  }
  · sorry

/-- In a list-arithmetic category, the list object is the initial algebra for the polynomial endofunctor `X ↦ 1 ⨿ A ⊗ X`. -/
noncomputable instance isInitialOflistAlgebra [ListArithmetic C] (A P : C)  :
    IsInitial (listAlgebra A) := by
  refine IsInitial.ofUniqueHom  (fun α => ?_) ?uniq
  · exact {
    f := plist.rc (initOfCoprodTensorEndofunctorAlgebra α) (actionOfcoprodTensorEndofunctorAlgebra α)
    h := by sorry
  }
  · sorry

/-- The Lambek isomorphism  `P ⨿ (A ⊗ plist A P) ≅ plist A P` -/
noncomputable def plistAlgebraIso  [ListArithmetic C] (A P : C) : P ⨿ (A ⊗ plist A P) ≅ plist A P where
  hom := (plistAlgebra A P).str
  inv := Algebra.Initial.strInv <| isInitialOfplistAlgebra A P
  hom_inv_id := Algebra.Initial.right_inv _
  inv_hom_id := Algebra.Initial.left_inv _

/-- The Lambek isomorphism  `1 ⨿ (A ⊗ list A) ≅ list A` -/
noncomputable def listAlgebraIso [ListArithmetic C] (A : C) :
    𝟙_ C ⨿ (A ⊗ list A) ≅ list A :=
  plistAlgebraIso A (𝟙_ C)

end listAsEndofunctorAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [ListArithmetic C]

open Recursive ListArithmetic

instance list.monObj (A : C) : MonObj (list A) where
  one := list.nil
  mul := list.append
  one_mul := list.whiskerRight_nil_append
  mul_one := list.whiskerLeft_nil_append
  mul_assoc := list.append_assoc

/--
The monoid structure on the list object in a list-arithmetic category.
-/
instance List.mon (A : C) : Mon C where
  X := list A


/-
Extra challenge:
Show that in the category of small categories,
an object with recursion is a monoidal category.
-/
