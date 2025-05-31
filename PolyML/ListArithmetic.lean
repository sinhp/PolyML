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

In category theory, the notion of parameterized list object models the list type, directly generalising Lawvere’s notion of NNO (Natural Numbers Object)

A **list object** on an object `A` in a category with finite products consists of an object `list A` and morphisms `nil : 𝟙_ C → list A` and `cons : A × list A  ⟶ list A`
which is initial among such data.

Such a structure is a **parameterized list object** whenever it is parametrized initial, i.e. it is initial among the data of `(P → L ← P × L)` for some parameter object `P` in the category.

In cartesian closed categories, these two notions coincide.

## Implementation notes

- We use a high-level definition of parameterized list object based on existence of a left adjoint to the forgetful functor from the category of actions to the underlying category `C`.
The advantage of this definition is that it gives a compact formulation of the universal property of the list object from which the recursion scheme can be derived thus enabling us to define all the important list maps. Such categories are called **recursive categories**. We can already define list maps such as `map`, `foldr` in recursive categories.

- The condition requiring the morphism `plist A (P ⊗ Y) ⟶ (plist A P) ⊗ Y` to be an isomorphism for all objects `A, P, Y` is equivalent to the requirment that the recursion in `C` is preserved when pulled back to the slice categories `C / P` for all `P`.

- Although parameterized list objects are defined in finite product categories, the well-behaved recursion scheme is only available in **list-arithmetic categories**, i.e. in categories with chosen finite products where the comparison morphisms `plist.cmp` are isomorphisms.

- In list-arithmetic categories, we can define additional list maps such as `append` and `flatten`.
-/

universe u v

noncomputable section
namespace CategoryTheory

open Functor Opposite Limits MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

open Endofunctor

/-
For an object `A` of a finite product product category `C`, an action of `A` on an object `S` is a morphism `A ⊗ S → S`. The pairs `(S, A ⊗ S → S)` are objects of the category `Act A`, constructed as the category of algebras for the left-tensoring endofunctor `A ⊗ -` on `C`. One may regard the objects of this category as state-changing alphabet `A` acting on sets of states `S`.
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

/-- An object `A` in a category `C` is called **recursive** if the forgetful functor from the category of actions on `A` to `C` has a left adjoint. -/
class HasRecursion (A : C) where
  /-- The Act.forgetful functor from the category of actions to the category `C` has a left adjoint. -/
  adj : IsRightAdjoint (Act.forget : Act A ⥤ C)

variable (C)

/-- A category `C` is called **recursive** if every object `A` in `C` is recursive. -/
class Recursive where
  has_rec (A : C) : HasRecursion A

namespace Recursive

variable {C} [Recursive C]

instance (A : C) : IsRightAdjoint (Act.forget : Act A ⥤ C) :=
  (Recursive.has_rec A).adj

def freeActionFunctor (A : C) : C ⥤ Act A := leftAdjoint (Act.forget : Act A ⥤ C)

def freeForgetAdj (A : C) : freeActionFunctor A ⊣ Act.forget  :=
  Adjunction.ofIsRightAdjoint (Act.forget : Act A ⥤ C)

/-- The mate of natural transformation `forget ⟶ map f ⋙ forget`. -/
def freeActionFunctorMapTriangle {A B : C} (f : A ⟶ B) :
    freeActionFunctor A ⟶ freeActionFunctor B ⋙ Act.map f :=
  mateEquiv (freeForgetAdj B) (freeForgetAdj A) |>.invFun <| Act.mapForgetTwoSquare f

/-- The paramtetrized list of `A` with the parameter object `P` .-/
def plist (A P : C) : C := freeActionFunctor A ⋙ Act.forget |>.obj P

namespace plist

def nil {A P : C} : P ⟶ plist A P := freeForgetAdj A |>.unit |>.app P

def cons {A P : C} : A ⊗ plist A P ⟶ plist A P :=
  freeActionFunctor A |>.obj P |>.str

/-- Covariant action of `plist` on morphisms of the first argument. -/
def map {A A' P : C} (f : A ⟶ A') : plist A P ⟶ plist A' P :=
  Act.forget.map <| freeActionFunctorMapTriangle f |>.app P

@[reassoc (attr := simp)]
theorem map_nil {A A' P : C} {f : A ⟶ A'} :
    (plist.nil : P ⟶ plist A P) ≫ plist.map f = plist.nil := by
  dsimp [plist.map, plist.nil]
  sorry

@[simp]
theorem map_cons {A A' P : C} {f : A ⟶ A'} :
    (plist.cons : A ⊗ plist A P ⟶ plist A P) ≫ plist.map f =
    (A ◁ plist.map f) ≫ (f ▷ plist A' P) ≫ plist.cons := by
  dsimp only [plist.map, plist.cons, Act.forget, Algebra.forget]
  simp only [← Act.hom, plist]
  congr 1

@[simp]
theorem map_id {A P : C} : plist.map (𝟙 A) = 𝟙 (plist A P) := by
  sorry

@[simp]
theorem map_comp {A A' A'' P : C} (f : A ⟶ A') (g : A' ⟶ A'') :
    plist.map (P:= P) (f ≫ g) = plist.map f ≫ plist.map g := by
  sorry

def functor (P : C) : C ⥤ C where
  obj A := plist A P
  map := plist.map
  map_id _ := plist.map_id
  map_comp := plist.map_comp

/-- The recursor morphism obtained as an adjoint transpose. -/
def rec {A P Y : C} (f : P ⟶ Y) (a : A ⊗ Y ⟶ Y) : plist A P ⟶ Y :=
  Act.forget.map <| freeForgetAdj A |>.homEquiv P ⟨Y, a⟩ |>.invFun f

@[reassoc (attr := simp)]
theorem rec_nil {A P Y : C} {f : P ⟶ Y} {a : A ⊗ Y ⟶ Y} :
    plist.nil ≫ plist.rec f a = f := by
  sorry

@[reassoc (attr := simp)]
theorem rec_cons {A P Y : C} {f : P ⟶ Y} {a : A ⊗ Y ⟶ Y} :
    plist.cons ≫ plist.rec f a = A ◁ (plist.rec f a) ≫ a := by
  sorry

@[simp]
theorem rec_uniq {A P Y : C} {f : P ⟶ Y} {a : A ⊗ Y ⟶ Y} (g : plist A P ⟶ Y)
    (hg₁ : plist.nil ≫ g = f) (hg₂ : plist.cons ≫ g = A ◁ g ≫ a) : g = plist.rec f a := by
  sorry

/-- The comparision morphism `plist A (P ⊗ Y) ⟶ (plist A P) ⊗ Y`. -/
def cmp (A P Y : C) : plist A (P ⊗ Y) ⟶ (plist A P) ⊗ Y :=
  plist.rec (plist.nil ▷ Y) ((α_ _ _ _).inv ≫ (plist.cons ▷ Y))

/-- `plist` is functorial in parameter `P`. -/
def map' (A : C) {P P' : C} (f : P ⟶ P') : plist A P ⟶ plist A P' :=
  Act.forget.map <| freeActionFunctor A |>.map f

theorem map'_eq_rec {A P P' : C} {f : P ⟶ P'} :
    (plist.map' A f) = plist.rec (f ≫ plist.nil) plist.cons := by
  sorry

instance map'_iso_of_iso {A P P' : C} (f : P ⟶ P') [IsIso f] :
    IsIso (plist.map' A f) := by
  sorry

end plist

/-- The list object defined as the recursive object with the terminal object as paramter `P`. -/
def list (A : C) : C := plist A (𝟙_ C)

namespace list

def nil {A : C} : 𝟙_ C ⟶ list A :=
  plist.nil (P := 𝟙_ C)

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
#check List.foldr

def map {A A' : C} (f : A ⟶ A') : list A ⟶ list A' :=
  plist.map (P := 𝟙_ C) f

def singleton {A : C} : A ⟶ list A :=
  (ρ_ A).inv ≫ (A ◁ (list.nil)) ≫ list.cons A

end list

/-- The natural numbers object (NNO) defined as the list object of the terminal object. -/
def nno : C :=
  list (𝟙_ C)

@[inherit_doc] notation "N" => nno

def nno.zero : 𝟙_ C ⟶ N :=
  list.nil

def nno.succ : (N : C) ⟶ N :=
  (λ_ _).inv ≫ list.cons (𝟙_ C)

def nno.one : 𝟙_ C ⟶ N :=
  nno.zero ≫ nno.succ

/-- The length of a list. -/
def list.len {A : C} : list A ⟶ N :=
  list.map <| toUnit A

/-- The length of the singleton list is `1`. -/
theorem list.singleton_len {A : C} :
    list.singleton ≫ list.len = toUnit A ≫ nno.zero ≫ nno.succ := by
  dsimp [list.singleton, list.len, nno.zero, nno.succ]
  sorry

end Recursive

open Recursive

variable [Recursive C]

/-- A recursive category is list-arithmetic if the comparison morphisms `cmp A P Y` are
all isomorphisms. -/
class ListArithmetic where
  is_iso {A P Y : C} : IsIso (plist.cmp A P Y)

namespace ListArithmetic

variable {C} [ListArithmetic C]

instance is_iso_instance {A P Y : C} : IsIso (plist.cmp A P Y) :=
  ListArithmetic.is_iso

/-- In a list-arithmetic category, `plist A P` is isomorphic to `(list A) ⊗ P`. -/
def plistIsoTensor (A P : C) : plist A P ≅ list A ⊗ P :=
  asIso (plist.map' A (λ_ P).inv ≫ plist.cmp A (𝟙_ C) P)

/-- Recursion scheme for the list object in a list-arithmetic category. -/
def list.rec {A P Y : C} (e : P ⟶ Y) (a : A ⊗ Y ⟶ Y) :
    list A ⊗ P ⟶ Y :=
  (plistIsoTensor A P).inv ≫ plist.rec e a

def list.foldr {A P Y : C} (a : A ⊗ Y ⟶ Y) (e : P ⟶ Y) :
    list A ⊗ P ⟶ Y :=
  list.rec e a

def nno.rec {P Y : C} (e : P ⟶ Y) (a : Y ⟶ Y) :
    N ⊗ P ⟶ Y :=
  list.rec e ((λ_ Y).hom ≫ a)

namespace list

theorem rec_nil {A P Y : C} {f : P ⟶ Y} {a : A ⊗ Y ⟶ Y} :
    ((λ_ P).inv ≫ list.nil ▷ P) ≫ list.rec f a = f := by
  sorry

/-- Appends two lists. -/
def append {A : C} : list A ⊗ list A ⟶ list A :=
  list.rec (𝟙 _) (list.cons A)

theorem nil_append {A : C} : list.nil ▷ list A ≫ list.append = (λ_ (list A)).hom := by
  sorry

theorem append_nil {A : C} : (list A ◁ list.nil) ≫ list.append = (ρ_ (list A)).hom := by
  sorry

theorem append_assoc {A : C} :
    list.append ▷ list A ≫ list.append =
    (α_ (list A) (list A) (list A)).hom ≫ list A ◁ list.append ≫ list.append := by
  sorry

/-- Reverses a list, i.e. the list with the elements in reverse order. -/
def rev {A : C} : list A ⟶ list A :=
  list.rec' list.nil ((list.singleton ▷ list A) ≫ (β_ _ _).hom ≫ list.append)

/-- list.rev is an involution, i.e. `list.rev ≫ list.rev = 𝟙`. -/
theorem rev_rev {A : C} :
    list.rev ≫ list.rev = 𝟙 (list A) := by
  sorry

/-- Concatenates a list of lists into a single list, preserving the order of the elements. -/
def flatten {A : C} : list (list A) ⟶ list A :=
  list.rec' list.nil list.append

end list

instance : CartesianMonoidalCategory (Type u) := sorry

instance : Recursive (Type u) where
  has_rec A := sorry

/-- The category of types is list-arithmetic. -/
instance : ListArithmetic (Type u) where
  is_iso := by
    sorry

end ListArithmetic

/-
In the presence finite coproducts, `list α` is the initial algebra for the polynomial functor
`P ↦ 1 + α × P`. The unique algebra map from `(List α, [n,c])` to
`(S,[s₀,s])` is the `foldr` function after transposition:
`foldr : (α → β → β) → β → List α → β`
satisfying
`foldr s s₀ n = s₀` and
`foldr s s₀ (c x xs) = s x (foldr s s₀ xs)`
-/


/-
Extra challenge:
Show that in the category of small categories, an object with recursion is a monoidal category.
-/


/-
We show that in a list-arithmetic category, the list object is
the free monoid object.
-/

variable [Recursive C] [ListArithmetic C]

open Recursive ListArithmetic

/--
The monoid structure on the list object in a list-arithmetic category.
-/
instance List.monoid (A : C) : Mon_ C where
  X := list A
  one := list.nil
  mul := list.append
  one_mul := list.nil_append
  mul_one := list.append_nil
  mul_assoc := list.append_assoc

def lift {A : C} {M : Mon_ C} (f : A ⟶ M.X) : list A ⟶ M.X :=
  sorry



-- The alternative (old) way to develop the theory of list arithmetic categories.
namespace List

/--
A list algebra on an object `A` in a category `C` cists of an object `L`
and morphisms `n : ⊤_C → L` and `c : A ⊗ L  ⟶ L`.
-/
structure Algebra (A : C) where
  L : C
  n : ⊤_C ⟶ L
  c : A ⊗ L  ⟶ L

namespace Algebra

variable {A : C}

/--
The list algberas on an object `A` in a category `C` form a category whose hom-types are given by the structure `Algebra.Hom`.
-/
@[ext]
structure Hom {A : C} (σ σ' : Algebra A) where
  hom : σ.L ⟶ σ'.L
  w_n : σ.n ≫ hom  = σ'.n := by aesop_cat
  w_c : σ.c ≫ hom  = A ◁ hom ≫ σ'.c := by aesop_cat

attribute [reassoc (attr := simp)] Hom.w_n Hom.w_c

instance category : Category (Algebra A) where
  Hom σ σ' := Hom σ σ'
  id L := ⟨𝟙 _, by aesop_cat, by aesop_cat⟩
  comp f g := ⟨f.hom ≫ g.hom, by aesop_cat, by aesop_cat⟩

/--
The initial list algebra.
-/
structure Initial (σ : Algebra A) where
  /-- For any list structure `σ'`, there is a morphism `desc` outgoing from `σ.obj` to `σ'.obj` -/
  desc : ∀ σ' : Algebra A, σ.L ⟶ σ'.L
  /-- For any list structure `σ'`, the morphism `desc` post-composed with `σ.n` is equal to `σ'.n` -/
  fac_n : ∀ σ' : Algebra A, σ.n ≫ desc σ' = σ'.n := by aesop_cat
  /-- For any list structure `σ'`, the morphism `desc` post-composed with `σ.c` is equal to `A ◁ lift σ' ≫ σ'.c` -/
  fac_c : ∀ σ' : Algebra A, σ.c ≫ desc σ' = A ◁ desc σ' ≫ σ'.c := by aesop_cat
  /-- For any list structure `σ'`, the morphism `desc` is unique -/
  uniq : ∀ σ' : Algebra A, ∀ (f : σ.L ⟶ σ'.L) (_ : σ.n ≫ f = σ'.n)
    (_ : σ.c ≫ f = A ◁ f ≫ σ'.c), f = desc σ' := by aesop_cat

/-- `IsInitial σ` represents the mere existence of an initial list algebra on `L`. -/
class IsInitial (σ : Algebra A) : Prop where mk' ::
  /-- there is an initial list algebra on L -/
  exists_initial : Nonempty (Initial σ)

theorem IsInitial.mk {σ : Algebra A} (i : Initial σ) : IsInitial σ :=
  ⟨Nonempty.intro i⟩

def getInitial (σ : Algebra A) [IsInitial σ] : Initial σ :=
  Classical.choice <| IsInitial.exists_initial

end Algebra

/--
An inital list algebra is the initial object in the category of list structures.
-/
def isInitial {A : C} (σ : Algebra A) (h : σ.IsInitial) : IsInitial σ := by
  have : ∀ Y : Algebra A, Unique (σ ⟶ Y) := by
    sorry
  apply IsInitial.ofUnique σ

variable (C)

/-- `HasList C` represents the mere existence of an initial list algebra on each object `A`. -/
class HasList : Prop where
  has_list : ∀ (A : C), ∃ (σ : Algebra A), σ.IsInitial

section

variable {C} [HasList C]

/-- The list object on `A : C` is the initial list algebra on `A`. -/
abbrev list' (A : C) : C :=
  HasList.has_list A |>.choose|>.L

abbrev list'.nil (A : C) : ⊤_C ⟶ list' A :=
  HasList.has_list A |>.choose|>.n

abbrev list'.cons (A : C) : A ⊗ list' A ⟶ list' A :=
  HasList.has_list A |>.choose|>.c

end

/-- The structure of a category with list objects. -/
class withList where
  /-- The list algebr on an object `A` in a category `C` is a list algebra. -/
  alg : ∀ (A : C), Algebra A
  /-- The list structure on an object `A` in a category `C` is initial. -/
  is_initial : ∀ (A : C), (alg A).Initial

variable {C} [withList C]

abbrev list (A : C)  : C :=
  withList.alg A |>.L

abbrev list.nil {A : C} : ⊤_C ⟶ list A :=
  withList.alg A |>.n

abbrev list.cons {A : C} : A ⊗ list A ⟶ list A :=
  withList.alg A |>.c

-- this is basically `List.foldr`
abbrev list.it {A P : C} (n : ⊤_C ⟶ P) (c : A ⊗ P ⟶ P) : list A ⟶ P :=
  withList.is_initial A |>.desc ⟨P, n, c⟩

end List

namespace PList

variable {C}

variable (P : C)

/--
The parametrized list algebra on an object `A` in a category `C` cists of an object `L`
and two morphisms `n : P → L` and `c : A ⊗ L → L`.
-/
structure Algebra (A : C) where
  L : C
  n : P ⟶ L
  c : A ⊗ L  ⟶ L

/--
The parametrized list algebra on an object `A` in a category `C` form a category whose hom-types are given by the structure `Algebra.Hom`.
-/
@[ext]
structure Hom {A : C} (σ σ' : Algebra P A) where
  hom : σ.L ⟶ σ'.L
  w_n : σ.n ≫ hom  = σ'.n := by aesop_cat
  w_c : σ.c ≫ hom  = A ◁ hom ≫ σ'.c := by aesop_cat

end PList


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
