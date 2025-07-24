/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Functor.TwoSquare
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Monoidal.Mon_


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

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

open Endofunctor Algebra

/-
For an object `A` of a finite product product category `C`, an action of `A` on an object `S` is a
morphism `A ⊗ S → S`. The pairs `(S, A ⊗ S → S)` are objects of the category `Act A`, constructed as the category
of algebras for the left-tensoring endofunctor `A ⊗ -` on `C`. One may regard the objects of this
category as state-changing alphabet `A` acting on sets of states `S`.
-/
private abbrev Act (A : C) := Algebra <| tensorLeft A

namespace Act

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

class WithRecursion (A : C) where
  freeActionFunctor : C ⥤ Act A
  freeForgetAdj : freeActionFunctor ⊣ Act.forget

/-- An object `A` in a category `C` is called **recursive** if the forgetful functor from the
category of actions on `A` to `C` has a left adjoint. -/
class HasRecursion (A : C) where
  /-- The Act.forgetful functor from the category of actions to the category `C` has a left adjoint. -/
  adj : IsRightAdjoint (Act.forget : Act A ⥤ C)

variable (C)

/-- A category `C` is called **recursive** if every object `A` in `C` is recursive. -/
class Recursive where
  withRec (A : C) : WithRecursion A

/-- A category `C` is called **recursive** if every object `A` in `C` is recursive. -/
class IsRecursive where
  has_rec (A : C) : HasRecursion A

namespace IsRecursive

variable {C} [IsRecursive C]

instance (A : C) : Functor.IsRightAdjoint (Act.forget : Act A ⥤ C) :=
  (IsRecursive.has_rec A).adj

noncomputable
def freeActionFunctor (A : C) : C ⥤ Act A := Functor.leftAdjoint (Act.forget : Act A ⥤ C)

noncomputable
def freeForgetAdj (A : C) : freeActionFunctor A ⊣ Act.forget  :=
  Adjunction.ofIsRightAdjoint (Act.forget : Act A ⥤ C)

end IsRecursive

namespace Recursive

variable {C} [Recursive C]

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
  simp only [Functor.map_comp, Adjunction.unit_naturality_assoc, Adjunction.right_triangle_components,
    comp_id]

theorem rec_cons {Y : C} {f : P ⟶ Y} {g : A ⊗ Y ⟶ Y} :
    plist.cons ≫ plist.rec f g = A ◁ plist.rec f g ≫ g := by
  dsimp [rec, cons, Adjunction.homEquiv]
  sorry

theorem rec_nil_cons_id : rec nil cons = 𝟙 (plist A P) := by
  sorry

/-- Covariant action of `plist` on morphisms of the first argument. -/
def map {B : C} (f : A ⟶ B) : plist A P ⟶ plist B P :=
  rec nil ((f ▷ (plist B P)) ≫ cons)

/-- Covariant action of `plist` on morphisms can be obtained as image of the component of the
natural transformation `Act.forget.map <| freeActionFunctorMapTriangle f` under the forgetful
functor `Act.forget : Act B ⥤ C`. -/
theorem map_nat_trans {B : C} {f : A ⟶ B} :
    map (P:= P) f = (Act.forget.map <| freeActionFunctorMapTriangle f |>.app P) := by
  sorry

@[reassoc (attr := simp)]
theorem map_nil {B: C} {f : A ⟶ B} : (nil : P ⟶ plist A P) ≫ map f = nil := by
  simp only [map, rec_nil]

@[reassoc (attr := simp)]
theorem map_cons {B : C} {f : A ⟶ B} :
    (cons : A ⊗ plist A P ⟶ plist A P) ≫ map f =
    (A ◁ map f) ≫ (f ▷ plist B P) ≫ cons := by
  simp only [map, rec_cons]

lemma whisker_map_nil {B: C} {f : A ⟶ B} : (A ◁ plist.nil) ≫ (A ◁ plist.map f (P := P)) = (A ◁ plist.nil) := by
   rw [← whiskerLeft_comp]
   simp only [map_nil]

@[simp]
theorem map_id : map (𝟙 A) = 𝟙 (plist A P) := by
  simp [map, rec_nil_cons_id]

@[simp]
theorem map_comp {A B B' P : C} (f : A ⟶ B) (g : B ⟶ B') :
    plist.map (P := P) (f ≫ g) = plist.map f ≫ plist.map g := by
  dsimp only [plist.map]
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
   (h : plist A P ⟶ C')
  (hh₁ : plist.nil ≫ h = f) (hh₂ : plist.cons ≫ h = A ◁ h ≫ g) :
    h = plist.rec f g := by {
    have Hnil: plist.nil ≫ plist.rec h g = h := rec_nil
    have Hcons : plist.cons ≫ plist.rec h g = A ◁ (plist.rec h g) ≫ g :=
       by {simp only [rec_cons]}
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

instance map'_iso_of_iso {A P P' : C} (f : P ⟶ P') [IsIso f] :
    IsIso (plist.map' A f) := by
  constructor
  sorry

end plist

/-- The list object defined as the recursive object
  with the terminal object as paramter `P`. -/
def list (A : C) : C := plist A (𝟙_ C)

namespace list

/- ε : 1 ⟶ list A -/
def nil {A : C} : 𝟙_ C ⟶ list A :=
  plist.nil (P := 𝟙_ C)

/- const : A × list A ⟶ list A -/
def cons (A : C) : A ⊗ list A ⟶ list A :=
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
    (list.cons A : A ⊗ list A ⟶ list A) ≫ list.map f =
    (A ◁ list.map f) ≫ (f ▷ list B) ≫ list.cons B := by
  simp only [list, list.cons, list.map, plist.map_cons]

@[simp]
theorem map_comp {A B B' : C} (f : A ⟶ B) (g : B ⟶ B') :
    list.map (f ≫ g) = list.map f ≫ list.map g := by
  simp only [list.map, plist.map_comp]

@[simp]
theorem map_id {A : C} : list.map (𝟙 A) = 𝟙 (list A) := by
  simp only [list.map, plist.map_id, list]

def singleton {A : C} : A ⟶ list A :=
  (ρ_ A).inv ≫ (A ◁ (list.nil)) ≫ list.cons A

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
  (λ_ _).inv ≫ list.cons (𝟙_ C)

def nno.one : 𝟙_ C ⟶ N_ C :=
  nno.zero ≫ nno.succ

/-- The length of a list. -/
def list.len {A : C} : list A ⟶ N_ C :=
  list.map <| toUnit A

open Category
/-- The length of the singleton list is `1`. -/
theorem list.singleton_len {A : C} :
    list.singleton ≫ list.len = toUnit A ≫ nno.zero ≫ nno.succ := by
    dsimp [nno.zero,nno.succ]
    dsimp [list.nil, list.len, singleton]
    simp only [assoc]
    nth_rw 1 [map_cons]
    rw [← assoc]
    rw [← assoc]
    rw [← assoc]
    rw [← assoc]
    rw [← assoc]
    refine ?_ =≫ cons (𝟙_ C)
    have : ((((ρ_ A).inv ≫ A ◁ plist.nil) ≫ A ◁ map (toUnit A))) =
      (((ρ_ A).inv ≫ (A ◁ plist.nil ≫ A ◁ map (toUnit A)))) :=
        by {exact assoc (ρ_ A).inv (A ◁ plist.nil) (A ◁ map (toUnit A))}
    rw [this]
    have : (A ◁ plist.nil) ≫ A ◁ map (toUnit A) = (A ◁ plist.nil) := by {
      refine hom_ext (A ◁ plist.nil ≫ A ◁ map (toUnit A)) (A ◁ plist.nil) ?_ ?_
      simp only [assoc, whiskerLeft_fst]
      simp only [assoc, whiskerLeft_snd, whiskerLeft_snd_assoc]
      refine snd A (𝟙_ C) ≫= ?_
      rw [← plist.map_nil (f := (toUnit A))]
      dsimp [list.map]
    }
    rw [this]
    rw [Iso.eq_comp_inv]
    simp only [assoc]
    sorry

end Recursive

open Recursive

variable [Recursive C]

class ListArithmetic' where
  is_iso {A P Y : C} : IsIso (plist.cmp A P Y)

/-- A recursive category is list-arithmetic if the comparison morphisms `cmp A P Y` are
all isomorphisms. -/
class ListArithmetic where
  cmpInv (A P Y : C) : plist A P ⊗ Y ⟶ plist A (P ⊗ Y)
  hom_inv_id : plist.cmp A P Y ≫ cmpInv A P Y = 𝟙 _
  inv_hom_id : cmpInv A P Y ≫ plist.cmp A P Y = 𝟙 _

namespace ListArithmetic

variable {C} [ListArithmetic C]

instance is_iso_instance {A P Y : C} : IsIso (plist.cmp A P Y) :=
  sorry --ListArithmetic.is_iso

/-- In a list-arithmetic category, `plist A B` is isomorphic to `(list A) ⊗ B`. -/
def plistIsoTensor (A B : C) : plist A B ≅ list A ⊗ B where
  hom := plist.map' A (λ_ B).inv ≫ plist.cmp A (𝟙_ C) B
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

  --asIso (plist.map' A (λ_ P).inv ≫ plist.cmp A (𝟙_ C) P)

/-- Recursion scheme for the list object in a list-arithmetic category. -/
def list.rec {A P Y : C} (e : P ⟶ Y) (a : A ⊗ Y ⟶ Y) :
    list A ⊗ P ⟶ Y :=
  (plistIsoTensor A P).inv ≫ plist.rec e a

def list.foldr {A P Y : C} (a : A ⊗ Y ⟶ Y) (e : P ⟶ Y) :
    list A ⊗ P ⟶ Y :=
  list.rec e a

def nno.rec {P Y : C} (e : P ⟶ Y) (a : Y ⟶ Y) :
    N_ C ⊗ P ⟶ Y :=
  list.rec e ((λ_ Y).hom ≫ a)

namespace list

theorem rec_nil {A P Y : C} {f : P ⟶ Y} {g : A ⊗ Y ⟶ Y} :
    ((λ_ P).inv ≫ list.nil ▷ P) ≫ list.rec f g = f := by
  simp only [Category.assoc]
  simp only [list, list.nil, list.rec]
  --simp only [comp_obj, comp_f, IsIso.Iso.inv_inv]
  nth_rw 2[← plist.rec_nil (f := f) (g := g)]
  --refine (IsIso.eq_inv_comp (λ_ P).inv).mp ?_
  --rw [IsIso.Iso.inv_inv]
  rw [← Category.assoc]
  rw [← Category.assoc]
  refine ?_ =≫ plist.rec f g
  refine (Iso.comp_inv_eq (plistIsoTensor A P)).mpr ?_
  --simp only [Category.assoc]
  --dsimp [plistIsoTensor, plist.map', plist.cmp]
  dsimp [plistIsoTensor]
  dsimp [plist.map']
  dsimp [plist.cmp]
  refine (Iso.inv_comp_eq (λ_ P)).mpr ?_
  sorry

/-- Appends two lists. -/
def append {A : C} : list A ⊗ list A ⟶ list A :=
  list.rec (𝟙 _) (list.cons A)

--plist A P ≅ list A ⊗ P

theorem nil_append {A : C} : list.nil ▷ list A ≫ list.append = (λ_ (list A)).hom := by
  dsimp [list,append, list.nil, list.cons]
  rw [← plist.map_id]


  sorry

  -- rw [← plist.map_id]
  -- rw [← plist.map_nil (f := (𝟙 A))]
  -- rw [← Category.assoc]
  -- rw [← rec_nil (f := (𝟙 A))]
  -- rw [plist.map_comp]
  -- unfold plist.rec
  -- simp only [plist.map_comp, plist.map_nil_assoc, plist.map_nil, Category.assoc,
  --   Equiv.invFun_as_coe]
  -- unfold freeActionFunctor
  -- unfold plist.nil
  -- unfold freeForgetAdj
  -- unfold Act.forget
  -- simp only [forget_obj, forget_map]
  -- simp?

theorem append_nil {A : C} : (list A ◁ list.nil) ≫ list.append = (ρ_ (list A)).hom := by
  dsimp [list.nil,list,append,list.cons]
  rw [← plist.map_id]
  simp only [plist.map_id, Category.comp_id, MonoidalCategory.whiskerLeft_id, Category.id_comp,
    plist.rec_uniq, plist.rec_nil]

  sorry

theorem append_assoc {A : C} :
    list.append ▷ list A ≫ list.append =
    (α_ (list A) (list A) (list A)).hom ≫ list A ◁ list.append ≫ list.append := by {
      sorry


     }
theorem map_append {A B : C} {f : A ⟶ B} :
    list.append ≫ list.map f = ((list.map f) ⊗ₘ (list.map f)) ≫ list.append := by
  dsimp [list.append, list.map]
  sorry

/-- Reverses a list, i.e. the list with the elements in reverse order. -/
def rev {A : C} : list A ⟶ list A :=
  list.rec' list.nil ((list.singleton ▷ list A) ≫ (β_ _ _).hom ≫ list.append)

/-- list.rev is an involution, i.e. `list.rev ≫ list.rev = 𝟙`. -/
theorem rev_rev {A : C} :
    list.rev ≫ list.rev = 𝟙 (list A) := by {
      sorry
    }

/-- Concatenates a list of lists into a single list, preserving the order of the elements. -/
def flatten {A : C} : list (list A) ⟶ list A :=
  list.rec' list.nil list.append

def mult {A : C} : list A ⟶ A := by
 apply list.rec'
 · sorry
 · sorry


def functor : C ⥤ C where
  obj A := list A
  map := list.map
  map_id _ := plist.map_id
  map_comp := plist.map_comp

end list

instance : CartesianMonoidalCategory (Type u) := sorry

instance : Recursive (Type u) where
  withRec := sorry

/-- The category of types is list-arithmetic. -/
instance : ListArithmetic (Type u) where
  cmpInv := sorry
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
variable [Recursive C] [ListArithmetic C]

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
