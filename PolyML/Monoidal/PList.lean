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

import PolyML.Monoidal.PNNO


/-!
# List Arithmetic Categories

In category theory, the notion of parameterized list object models the list type, directly
generalising Lawvere’s notion of NNO (Natural Numbers Object)

A **list object** on an object `A` in a monoidal category consists of an object `L A`
and morphisms `nil A : 𝟙_ C → L A` and `cons A : A ⊗ L A  ⟶ L A`
which is initial among such data. The initiality gives rise to a recursion scheme for lists.

A list object is **parameterized** if the recursion scheme is stable under pullback to the slice
categories, that is, for all objects `P`, the list object in the slice category `C / P` is given by
`L A ⊗ P`

In cartesian closed categories, the notions of list object and parameterized list object coincide.

## Implementation Notes

We define the type class `PList A` carrying the data of an object `L A` along with the morphisms
`nil A` and `cons A` and the universal property of the parameterized list object.

We show that having an instance of `PList A` gives rise to a left adjoint to the forgetful functor
from the category of left actions of `A : C` to the base monoidal category `C`.
This adjunction in fact captures all aspects of the list object, including the universal property.

### Main definitions

- `PList.map f : L A ⟶ L B` : Given a morphism `f : A ⟶ B`, induces
  a morphism `L A ⟶ L B`.

- `PList.foldr g : L A ⊗ B ⟶ B` : The foldr morphism for lists, generalizing the foldr operation on lists in
  functional programming languages.

- `PList.singleton A : A ⟶ PList.L A` : The singleton list morphism.

- `PList.append A : L A ⊗ L A ⟶ L A` : The append morphism for lists.

- `PList.rev A : L A ⟶ L A` : The list reversal morphism.

- `PList.flatten A : L (L A) ⟶ L A` : The flatten morphism concatenating a list of lists.

- `PList.snoc A : L A ⊗ A ⟶ L A` : The snoc morphism adding an element to the end of a list.

- `PList.splitHeadTail A P : L A ⊗ P ⟶ P ⨿ (A ⊗ L A) ⊗ P` : The head-tail splitting morphism for
  lists, generalizing pattern matching on lists into head and tail using coproducts.

- `PList.tail? A : L A ⟶ 𝟙_ C ⨿ L A` : Drops the first element of a nonempty list,
  returning the tail. Returns none when the argument is empty.

- `PList.splitAt : L A ⊗ N ⟶ L A ⊗ L A` : The splitAt morphism splitting a list at a given numeral
  index into two sublists.

-/


universe u v

namespace CategoryTheory

open Category Opposite Limits MonoidalCategory

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

namespace MonoidalCategory

open Endofunctor Algebra

section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

class IsPList (A : C) (L : C) (nil : 𝟙_ C ⟶ L) (cons : A ⊗ L ⟶ L) where
  /-- The recursor morphism for the parameterized list object. -/
  prc {P B : C} (f : P ⟶ B) (g : A ⊗ B ⟶ B) : L ⊗ P ⟶ B
  /-- The nil case of the recursor. -/
  nil_prc {P B : C} {f : P ⟶ B} {g : A ⊗ B ⟶ B} :
    (nil ▷ P) ≫ prc f g = (λ_ P).hom ≫ f
  /-- The cons case of the recursor. -/
  cons_prc {P B : C} {f : P ⟶ B} {g : A ⊗ B ⟶ B} :
    (α_ _ _ _).inv ≫ (cons ▷ P) ≫ prc f g = (A ◁ prc f g) ≫ g
  /-- The uniqueness of the recursor. -/
  prc_uniq {P B : C} {f : P ⟶ B} {g : A ⊗ B ⟶ B} (r : L ⊗ P ⟶ B)
    (h_nil : (nil ▷ P) ≫ r = (λ_ P).hom ≫ f)
    (h_cons: (α_ _ _ _).inv ≫ (cons ▷ P) ≫ r =  A ◁ r ≫ g) : r = prc f g

attribute [reassoc (attr := simp)] IsPList.nil_prc IsPList.cons_prc

class PList (A : C) where
  /-- The underlying list object on `A`. -/
  L : C
  /-- The nil morphism for the list object `L A`. -/
  nil (A) : 𝟙_ C ⟶ L
  /-- The cons morphism for the list object `L A`. -/
  cons (A) : A ⊗ L ⟶ L
  /-- The universal property of the parameterized list object. -/
  [isPList : IsPList A L nil cons]

attribute [instance] PList.isPList

end

namespace PList

open IsPList

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable {A : C} [PList A]

abbrev prc {P B : C} (f : P ⟶ B) (g : A ⊗ B ⟶ B) :
    PList.L A ⊗ P ⟶ B :=
  IsPList.prc (PList.nil A) (PList.cons A) f g

abbrev rc {B : C} (f : 𝟙_ C ⟶ B) (g : A ⊗ B ⟶ B) :
    PList.L A ⟶ B :=
  (ρ_ _).inv ≫ prc f g

@[simp]
lemma rightUnitor_unit_inv_nil_whisker_rightUnitor_unit_hom :
    (ρ_ (𝟙_ C)).inv ≫ (nil A ▷ (𝟙_ C)) ≫ (ρ_ (PList.L A)).hom = nil A := by
  sorry

theorem prc_nil_cons_id {P : C} :
    prc ((λ_ P).inv ≫ nil A ▷ P) ((α_ _ _ _).inv ≫ cons A ▷ P) = 𝟙 (PList.L A ⊗ P) :=
  sorry

/-- Covariant action of `PList` on morphisms of the first argument.
A morphism `f : A ⟶ B` induces a morphism `PList.map f : PList.L A ⊗ P ⟶ PList.L B ⊗ P`. -/
def map' {A' : C} [PList A'] (P : C) (f : A ⟶ A') :
    PList.L A ⊗ P ⟶ PList.L A' ⊗ P :=
  prc ((λ_ P).inv ≫ nil A' ▷ P) (f ▷ (L A' ⊗ P) ≫ (α_ _ _ _).inv ≫ cons A' ▷ P)

/-- Covariant action of `PList` on morphisms of the first argument.
A morphism `f : A ⟶ B` induces a morphism `PList.map f ▷ P : PList.L A ⊗ P ⟶ PList.L B ⊗ P`. -/
def map {A' : C} [PList A'] (f : A ⟶ A') :
    PList.L A ⟶ PList.L A' :=
  rc (nil A') (f ▷ (L A') ≫ cons A')

theorem map_map' {A' : C} [PList A'] {f : A ⟶ A'} :
    map f = (ρ_ _).inv ≫ map' (𝟙_ C) f ≫ (ρ_ _).hom := by
  sorry

theorem map'_map {A' : C} [PList A'] {P : C} {f : A ⟶ A'} :
    map' P f = map f ▷ P := by
  dsimp [map, map']
  sorry

@[reassoc (attr := simp)]
theorem nil_map {A' : C} [PList A'] {P : C} (f : A ⟶ A') :
    nil A ≫ map f = nil A' := by
  simp [map, rc]
  sorry

@[reassoc (attr := simp)]
theorem cons_map' {A' : C} [PList A'] {P : C} {f : A ⟶ A'} :
    cons A ▷ P ≫ (map f ▷ P) =
      (α_ _ _ _).hom ≫ (f ⊗ₘ (map f ▷ P)) ≫ (α_ _ _ _).inv ≫ cons A' ▷ P := by
  sorry

theorem cons_map {A' : C} [PList A'] {f : A ⟶ A'} :
    cons A ≫ map f = (f ⊗ₘ map f) ≫ cons A' := by
  dsimp [map, rc]
  sorry


theorem map_id : map (𝟙 A) = 𝟙 (PList.L A) := by
  sorry

@[reassoc (attr := simp)]
theorem map_comp {A' A'' : C} [PList A'] [PList A''] (f : A ⟶ A') (g : A' ⟶ A'') :
  map (f ≫ g) = (map f ≫ map g) := by
  dsimp [map, prc, map', rc]
  rw [← IsPList.prc_uniq] <;> sorry

/-- The `foldr` morphism. In types, `[a, b, c].foldr g init  = g a (g b (g c init))`. -/
def foldr {B : C} (g : A ⊗ B ⟶ B) : L A ⊗ B ⟶ B := prc (𝟙 B) g

@[reassoc (attr := simp)]
theorem foldr_nil {B : C} (g : A ⊗ B ⟶ B) :
  nil A ▷ B ≫ foldr g = (λ_ B).hom := by
  dsimp [foldr]
  sorry

@[simp]
theorem foldr_cons {B : C} (g : A ⊗ B ⟶ B) :
  cons A ▷ B ≫ foldr g = (α_ _ _ _).hom ≫ (A ◁ foldr g) ≫ g := by
  dsimp [foldr]
  sorry

variable (A)

/-- The singleton list morphism. In types, `singleton a = [a]`. -/
def singleton : A ⟶ L A :=
  (ρ_ _).inv ≫ (A ◁ nil A) ≫ cons A

/-- Appends two lists. -/
def append : L A ⊗ L A ⟶ L A := foldr (cons A)

section append

variable {A}

theorem append_prc : append A = prc (𝟙 _) (cons A) := by
  simp only [append, foldr]

@[reassoc (attr := simp)]
theorem nil_append : nil A ▷ (L A) ≫ append A = (λ_ (L A)).hom := by
  simp [append]

--xs ++ [] = xs
theorem append_nil : (L A) ◁ nil A ≫ append A = (ρ_ (L A)).hom := by
  sorry

-- (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
theorem append_assoc :
    append A ▷ (L A) ≫ append A = (α_ _ _ _).hom ≫ ((L A) ◁ append A) ≫ append A := by
  sorry

-- map f (xs ++ ys) = map f xs ++ map f ys
theorem append_map {A' : C} [PList A'] {f : A ⟶ A'} :
    append A ≫ map f = ((map f) ⊗ₘ (map f)) ≫ append A' := by
  sorry

-- [x] ++ xs = x :: xs
@[reassoc (attr := simp)]
theorem singleton_append : (singleton A ▷ L A) ≫ append A = cons A := by
  dsimp [append, singleton]
  simp only [comp_whiskerRight, whisker_assoc, assoc, triangle_assoc_comp_right_inv_assoc, foldr]
  rw [cons_prc]
  sorry

end append


/-- The monoid object structure on the list object given by `nil` and `append`. -/
instance addMonObj : AddMonObj (L A) where
  zero := nil A
  add := append A
  zero_add := nil_append
  add_zero := append_nil
  add_assoc := append_assoc

@[simps]
def addMon : AddMon C := AddMon.mk (L A)

def snoc : L A ⊗ A ⟶ L A := (L A ◁ singleton A) ≫ append A

theorem braiding_list_unit_hom [BraidedCategory C] [PList (𝟙_ C)] {P : C} :
    (β_ (L (𝟙_ C)) P).hom = prc ((ρ_ P).inv ≫ P ◁ nil (𝟙_ C)) (λ_ _).hom := by
  sorry

/-- Reverses a list, i.e. the list with the elements in reverse order. -/
def rev [BraidedCategory C] : L A ⟶ L A :=
  rc (nil A) ((singleton A ▷ L A) ≫ (β_ _ _).hom ≫ append A)

section rev

variable {A}

/- rev_nil [] = [] -/
theorem nil_rev [BraidedCategory C] : nil A ≫ rev A = nil (A := A) := by
  dsimp [rev, nil, prc]
  sorry

/- rev [x] = [x] -/
theorem singleton_rev_eq_singleton [BraidedCategory C] : singleton A ≫ rev A = singleton A := by
  simp only [rev, singleton]
  sorry

/- rev (xs ++ ys) = rev ys ++ rev xs -/
theorem rev_append [BraidedCategory C] :
    append A ≫ rev A = (rev A ⊗ₘ rev A) ≫ append A := by
  sorry

/- rev (rev xs ++ [x]) = [x] ++ xs -/
theorem singleton_braiding_append_rev_eq_singleton_append [BraidedCategory C] :
    ((singleton A ▷ L A) ≫ (β_ _ _).hom ≫ append A ≫ rev A) =
    (singleton A ▷ L A) ≫ append A := by
  sorry

/-- rev is an involution, i.e. `rev ≫ rev = 𝟙`. -/
theorem rev_rev [BraidedCategory C] : rev A ≫ rev A = 𝟙 (L A) :=
  sorry

end rev

/-- Concatenates a list of lists into a single list, preserving the order of the elements. -/
def flatten [PList (L A)] : L (L A) ⟶ L A :=
  rc (nil A) (append A)

/-- splits a list into its head and tail, if the list is non-empty, else returns the empty list. -/
noncomputable def splitHeadTail (P : C) [HasBinaryCoproducts C] : L A ⊗ P ⟶ P ⨿ (A ⊗ L A) ⊗ P :=
  prc (coprod.inl) ((A ◁ coprod.desc ((λ_ _).inv ≫ (nil A ▷ P)) (cons A ▷ P)) ≫ (α_ _ _ _).inv ≫ coprod.inr)

section splitHeadTail

variable {A} {P : C} [HasBinaryCoproducts C]


-- splitHeadTail [] = inl ()
@[reassoc (attr := simp)]
theorem nil_splitHeadTail : (nil A ▷ P) ≫ splitHeadTail A P = (λ_ _).hom ≫ coprod.inl := by
  dsimp [splitHeadTail]
  sorry

-- `fun (a, as) => splitHeadTail (a :: as) = fun (a, as) => inr (a, as)`
@[reassoc (attr := simp)]
theorem cons_splitHeadTail : (cons A ▷ P) ≫ splitHeadTail A P = coprod.inr := by
  dsimp [splitHeadTail]
  sorry

-- `fun as => if splitHeadTail (as) = inl (nil) return nil else cons splitHeadTail as = fun as => as`
@[reassoc (attr := simp)]
theorem splitHeadTail_nil_cons :
    splitHeadTail A P ≫ coprod.desc ((λ_ _).inv ≫ (nil A ▷ P)) (cons A ▷ P) = 𝟙 (L A ⊗ P) := by
  dsimp [splitHeadTail]
  sorry

end splitHeadTail

@[simps]
noncomputable def splitHeadTailIso [HasBinaryCoproducts C] (P : C) : L A ⊗ P ≅ P ⨿ (A ⊗ L A) ⊗ P where
  hom := splitHeadTail A P
  inv := coprod.desc ((λ_ _).inv ≫ (nil A ▷ P)) (cons A ▷ P)
  hom_inv_id := splitHeadTail_nil_cons
  inv_hom_id := by
    refine coprod.hom_ext ?_ ?_
    · simp only [coprod.desc_comp, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.ι_app_left,
      BinaryCofan.mk_inl, comp_id]
      rw [assoc, Iso.inv_comp_eq]
      exact nil_splitHeadTail
    · simp only [coprod.desc_comp, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.ι_app_right,
      BinaryCofan.mk_inr, comp_id]
      exact cons_splitHeadTail

/-- takes a pair of lists `(as, bs)` and returns `(as, nil)` if `bs` is `nil`, else removes the head of `bs`,
and attaches it to the end of `as`. -/
noncomputable def shunt [HasBinaryCoproducts C] [BraidedCategory C] : L A ⊗ L A ⟶ L A ⊗ L A :=
  (β_ (L A) (L A)).hom ≫
    splitHeadTail A (L A) ≫
      (coprod.map (𝟙 _) ((β_ (A ⊗ L A) (L A)).hom ≫ (α_ _ _ _).inv)) ≫
        coprod.desc ((ρ_ _).inv ≫ (L A ◁ nil A )) (snoc A ▷ L A)

section shunt

variable {A} [HasBinaryCoproducts C] [BraidedCategory C]

-- shunt as [] = as []
@[reassoc (attr := simp)]
theorem nil_shunt : (L A ◁ nil A) ≫ shunt A = L A ◁ (nil A) := by
  dsimp [shunt]
  sorry

@[reassoc (attr := simp)]
theorem cons_shunt : (L A ◁ cons A) ≫ shunt A = (α_ _ _ _).inv ≫ (snoc A ▷ L A) := by
  dsimp [shunt]
  sorry

end shunt

end PList

/-
For an object `A` of a finite product product category `C`, an action of `A` on an object `S` is a
morphism `A ⊗ S → S`. The pairs `(S, A ⊗ S → S)` are objects of the category `Act A`, constructed as the category
of algebras for the left-tensoring endofunctor `A ⊗ -` on `C`. One may regard the objects of this
category as state-changing alphabet `A` acting on sets of states `S`.
-/
abbrev Act {C : Type u} [Category.{v} C] [MonoidalCategory C] (A : C) := Algebra <| tensorLeft A

namespace Act

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

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

section

open IsPList PList

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The left `A`-action on `PList A ⊗ P`. -/
@[simps! +simpRhs a str]
def PList.act (A : C) [PList A] (P : C) : Act A where
  a := PList.L A ⊗ P
  str := (α_ _ _ _).inv ≫ PList.cons A ▷ P

/-- An object `A` in a category `C` is said to have **recursion** if there is a functor from `C` to
the category of left `A`-actions which is left adjoint to the forgetful functor. -/
class WithRecursion (A : C) where
  freeActionFunctor (A) : C ⥤ Act A
  freeForgetAdj (A) : freeActionFunctor ⊣ Act.forget

end

namespace WithRecursion

open PList IsPList

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The mate of natural transformation `forget ⟶ map f ⋙ forget`. -/
def freeActionFunctorMapTriangle {A B : C} [WithRecursion A]
    [WithRecursion B] (f : A ⟶ B) :
    freeActionFunctor A ⟶ freeActionFunctor B ⋙ Act.map f :=
  mateEquiv (freeForgetAdj B) (freeForgetAdj A) |>.invFun <| Act.mapForgetTwoSquare f

theorem freeActionFunctorMapTriangle_id {A : C} [WithRecursion A] :
    IsIso <| freeActionFunctorMapTriangle (𝟙 A) := by
  sorry

/-- A list object provides a left adjoint to the forgetful functor from `Act A` to `C`. -/
instance ofPList (A : C) [PList A] : WithRecursion A where
  freeActionFunctor := {
    obj P := PList.act A P
    map {P Q} φ := {
      f := PList.L A ◁ φ
      h := by
        simp only [PList.act_a, curriedTensor_obj_obj, curriedTensor_obj_map, PList.act_str, assoc]
        rw [associator_inv_naturality_right_assoc, ← whisker_exchange]
    }
  }
  freeForgetAdj.unit.app P := (λ_ _).inv ≫ (PList.nil A) ▷ P
  freeForgetAdj.counit.app β := {
    f := prc (nil := PList.nil A) (cons := PList.cons A) (𝟙 (β.a)) β.str
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

@[simp]
theorem ofPList.freeActionFunctor_forget_obj :
    (freeActionFunctor A ⋙ Act.forget).obj P = PList.L A ⊗ P :=
  rfl

@[simp]
theorem ofPList.freeForgetAdj_unit_app :
    (freeForgetAdj A |>.unit).app P = (λ_ _).inv ≫ (PList.nil A) ▷ P :=
  rfl

@[simp]
theorem withRecursionOfPList.freeActionFunctor_obj_str :
    (freeActionFunctor A |>.obj P).str = (α_ _ _ _).inv ≫ PList.cons A ▷ P :=
  rfl

@[simp]
theorem ofPList.forgetMap_freeForgetAdj_homEquiv {B : C} (f : P ⟶ B) (g : A ⊗ B ⟶ B) :
    (Act.forget.map <| freeForgetAdj A |>.homEquiv P ⟨B, g⟩ |>.invFun f) = prc f g := by
  sorry

@[simp]
theorem ofPList.freeActionFunctor_map_forget {Q : C} (φ : P ⟶ Q) :
    (freeActionFunctor A |>.map φ).f =
      prc (φ ≫ (λ_ Q).inv ≫ PList.nil A ▷ Q) ((α_ _ _ _).inv ≫ PList.cons A ▷ Q) := by
  sorry

@[simp]
theorem ofPList.forget_freeActionFunctor_map {Q : C} (φ : P ⟶ Q) :
    (Act.forget.map <| freeActionFunctor A |>.map φ) =
      PList.L A ◁ φ := by
  rfl

@[simp]
theorem ofPList.forgetMap_freeActionFrunctorTrianlge_app {A' : C} [PList A'] {f : A ⟶ A'}  :
    (Act.forget.map <| freeActionFunctorMapTriangle f |>.app P) = map f ▷ P := by
  dsimp [Adjunction.homEquiv, freeActionFunctorMapTriangle]
  simp only [Act.mapForgetTwoSquare,Act.mapForgetIsoSquare,Act.mapForgetIso]
  simp only [Functor.map_id, comp_id, id_comp]
  dsimp [Act.forget, forget_map, Act.map]
  simp only [Functor.map_id, id_f, id_comp]
  sorry

end

end WithRecursion

section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

@[simps]
def IsPNNO.ofPListUnitNilCons [PList (𝟙_ C)] :
    IsPNNO (PList.L (𝟙_ C)) (PList.nil (𝟙_ C)) ((λ_ _).inv ≫ PList.cons (𝟙_ C)) where
  prc {P B} f g := PList.prc f ((λ_ _).hom ≫ g)
  zero_prc {P B f g} := by simp
  succ_prc {P B f g} := by simp
  prc_uniq {P B f g r h_nil h_cons} := by
    apply IsPList.prc_uniq r h_nil
    rw [comp_whiskerRight, assoc] at h_cons
    rw [leftUnitor_inv_whiskerRight, assoc, Iso.inv_comp_eq] at h_cons
    simpa using h_cons

/-- A list object for the unit object gives rise to a parameterized natural number object. -/
@[simps]
def PNNO.ofPListUnit [PList (𝟙_ C)] : PNNO C where
  N := PList.L (𝟙_ C)
  zero := PList.nil (𝟙_ C)
  succ := (λ_ _).inv ≫ PList.cons (𝟙_ C)
  isPNNO := IsPNNO.ofPListUnitNilCons

/-- An isomorphism between the parameterized list object on the unit and the natural number object. -/
@[simps!]
def PList.ofUnitIsoNNO [PList (𝟙_ C)] [PNNO C] : PList.L (𝟙_ C) ≅ PNNO.N :=
  @IsPNNO.iso _ _ _  (PNNO.ofPListUnit.N) PNNO.N _ _ _ _ PNNO.ofPListUnit.isPNNO PNNO.isPNNO

end

namespace PList

section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (A : C) [PList A]

attribute [local instance] PNNO.ofPListUnit

/-- Splits a list at an index `n` , resulting in the first `n` elements of the list paired with the remaining
elements. -/
noncomputable def splitAt [PNNO C] [HasBinaryCoproducts C] [BraidedCategory C] :
    PNNO.N ⊗ L A ⟶ L A ⊗ L A :=
  PNNO.prc ((λ_ _).inv ≫ (nil A ▷ L A)) (shunt A)

section splitAt

variable {A} [PList (𝟙_ C)] [HasBinaryCoproducts C] [BraidedCategory C]

-- splitAt 0 xs = ([], xs)
@[reassoc (attr := simp)]
theorem splitAt_zero :
    (PNNO.zero ▷ L A) ≫ splitAt A = (nil A ▷ L A) := by
  dsimp [splitAt]
  sorry

@[reassoc (attr := simp)]
-- splitAt (succ n) xs = let (ys, zs) = splitAt n xs in shunt ys zs
theorem splitAt_succ : (PNNO.succ ▷ L A) ≫ splitAt A = (splitAt A) ≫ shunt A := by
  dsimp [splitAt]
  sorry

end splitAt

end

open PList SemiCartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [SemiCartesianMonoidalCategory C] {A : C} [PList A] {P : C}

theorem prc_id_snd_snd : prc (𝟙 P) (snd A P) = snd (L A) P := by
  sorry

/-- The length of a list. -/
abbrev len [PList (𝟙_ C)] : L A ⟶ PNNO.ofPListUnit.N :=
  PList.map <| SemiCartesianMonoidalCategory.toUnit A

section length

open SemiCartesianMonoidalCategory PList PNNO

variable [PList (𝟙_ C)]

attribute [local instance] PNNO.ofPListUnit

theorem len_eq_rc_zero_snd_succ :
    len = PList.rc zero (snd A N ≫ succ) := by
  dsimp [len]
  rw [Iso.eq_inv_comp]
  apply IsPList.prc_uniq
  · dsimp [nil, len, map, map]
    sorry
  . dsimp [len, PList.map, PList.cons]
    sorry

@[reassoc (attr := simp)]
theorem nil_len_zero : nil (A:= A) ≫ len = zero := by
  simp [len_eq_rc_zero_snd_succ, PList.rc]
  sorry

-- len (a :: xs) = succ (len xs)
theorem cons_len_succ :
    cons A ≫ len = (A ◁ len) ≫ snd A N ≫ succ := by
  dsimp [len]
  rw [cons_map]
  rw [← Category.assoc]
  sorry

theorem cons_len_eq_map_toUnit_cons :
    cons A ≫ len = A ◁ map (toUnit A) ≫ (toUnit A ▷ L (𝟙_ C)) ≫ cons (𝟙_ C) := by
  dsimp [len, PList.cons]
  rw [PList.cons_map]
  sorry

-- len (xs ++ ys) = len xs + len ys
theorem append_len_add : append (A:= A) ≫ len = (len ⊗ₘ len) ≫ add := by
  sorry


-- len ([x]) = 1
theorem singleton_len_one :
    singleton A ≫ len = toUnit A ≫ one := by
  sorry

/-- The length function is a monoid homomorphism from the list monoid to the natural number object. -/
instance isAddMonHomLen [BraidedCategory C] : IsAddMonHom (len (A:= A)) where
  zero_hom := nil_len_zero
  add_hom := append_len_add

/-- Promoting the length morphism to an internal monoid homomorphism from `L A` to `N`. -/
def lenAddMonHom [BraidedCategory C] :
    AddMon.Hom (PList.addMon A) (PNNO.addMon) where
  hom := len
  isMonHom_hom := by infer_instance

end length

end PList

abbrev WithPList (C : Type u) [Category.{v} C] [MonoidalCategory C] := Π (A : C), PList A

end MonoidalCategory

section PListAsEndofunctorAlgebra

open PList

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasBinaryCoproducts C]

namespace Endofunctor

/-- The linear polynomial endofunctor `X ↦ P ⨿ (A ⊗ X)` on the category `C`. -/
noncomputable def linearPolynomial (A P : C) : C ⥤ C where
  obj X := P ⨿ (A ⊗ X)
  map {X Y} f := coprod.map (𝟙 _) (A ◁ f)

/-- The algebra associated to a pair `init : P ⟶ X` and `action A ⊗ X ⟶ X` of morphisms for the endofunctor `X ↦ P ⨿ (A ⊗ X)`. -/
noncomputable def linearPolynomialAlgebraMk {A P} (X : C) (nil : P ⟶ X) (cons : A ⊗ X ⟶ X) :
    Algebra (linearPolynomial A P) := ⟨X, coprod.desc nil cons⟩


/-- The init morphism `P ⟶ α.a` for an algebra of the endofunctor `X ↦ P ⨿ (A ⊗ X)`. -/
noncomputable def linearPolynomialAlgebra.nil {A P : C}
    (α : Algebra (linearPolynomial A P)) :
  P ⟶ α.a := coprod.inl ≫ α.str

/-- The action morphism `A ⊗ α.a ⟶ α.a` for an algebra of the endofunctor `X ↦ P ⨿ (A ⊗ X)`. -/
noncomputable def linearPolynomialAlgebra.cons {A P : C}
    (α : Algebra (linearPolynomial A P)) : A ⊗ α.a ⟶ α.a :=
  coprod.inr ≫ α.str

namespace Algebra

/-- The algebra associated to the parameterized list object `plist A P` for the endofunctor `X ↦ P ⨿ (A ⊗ X)`. -/
noncomputable def ofPList (A P : C) [PList A] :
    Algebra (linearPolynomial A P) :=
  linearPolynomialAlgebraMk (L A ⊗ P) ((λ_ _).inv ≫ nil A ▷ P) ((α_ A (L A) P).inv ≫ cons A ▷ P)

theorem OfPList_a {A P : C} [PList A] :
    (ofPList A P).a = L A ⊗ P := by
  rfl

theorem ofPList_str {A P : C} [PList A] :
    (ofPList A P).str =
      coprod.desc ((λ_ _).inv ≫ nil A ▷ P) ((α_ A (L A) P).inv ≫ cons A ▷ P) := by
  rfl

/-- In a list-arithmetic category, the parametrize list object is the initial algebra for the
polynomial  endofunctor `X ↦ P ⨿ A ⊗ X`. -/
noncomputable instance ofPListIsInitial {A P : C} [PList A] :
    IsInitial (Endofunctor.Algebra.ofPList A P) := by
  refine IsInitial.ofUniqueHom  (fun α => ?_) ?uniq
  · exact {
    f := prc (linearPolynomialAlgebra.nil α) (linearPolynomialAlgebra.cons α)
    h := by sorry
  }
  · sorry

/-- Conversely, any initial algebra for the polynomial endofunctor `X ↦ P ⨿ A ⊗ X` gives rise to a
parameterized list object. -/
noncomputable def toPList (A P : C)
    (α : Algebra (linearPolynomial A P)) (h : IsInitial α):
    PList A where
  L := sorry -- extract L A from α.a ≅ L A ⊗ P
  nil := sorry
  cons := sorry
  isPList := sorry

/-- The Lambek isomorphism  `P ⨿ (A ⊗ plist A P) ≅ plist A P` -/
noncomputable def isoOfPList (A P : C) [PList A] : P ⨿ (A ⊗ L A ⊗ P) ≅ L A ⊗ P where
  hom := (ofPList A P).str
  inv := Algebra.Initial.strInv <| ofPListIsInitial
  hom_inv_id := Algebra.Initial.right_inv _
  inv_hom_id := Algebra.Initial.left_inv _

end Algebra

end Endofunctor

end PListAsEndofunctorAlgebra

end CategoryTheory
