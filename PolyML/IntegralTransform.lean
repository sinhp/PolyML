-- import CatML.Polynomial

import Mathlib.Data.Finset.Basic

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.FintypeCat

import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Monad.Algebra

import Mathlib.CategoryTheory.Endofunctor.Algebra


/-
1. Categorify the list construction
2. Categorify the bag construction
2. Make computable monads out of a general polynomial functor
3. Given a span, write a polynomial functor and the associated monad
4. computing with that monad extract the GNN/DP algorithm (maps from span to GNN and separately to DP)
-/

/-
`List α` is the initial algebra for the polynomial functor `X ↦ 1 + α × X` in
the category of types. The unique algebra map from (List α, [nil,cons]) to
(S,[s₀,s]) is the foldr function after transposition.
[]
`foldr : (α → β → β) → β → List α → β`
satisfying
`foldr s s₀ nil = s₀` and
`foldr s s₀ (cons x xs) = s x (foldr s s₀ xs)`
-/


universe u v

noncomputable section
namespace CategoryTheory

open Functor Opposite Limits Endofunctor List

#check List
#check List.foldr


variable {C : Type (u + 1)} [Category C] [HasBinaryCoproducts C] [HasBinaryProducts C] [HasTerminal C]

def LP (A : C) : C ⥤ C where
  obj X := (⊤_ C) ⨿ (A ⨯ X)
  map {X Y} f := coprod.map (𝟙 _) (prod.map (𝟙 A) f)


/-- The list object in a category with products and coproducts. -/
def List (A : C) [HasInitial (Algebra (LP A))] :=  (⊥_ (Algebra (LP A))).a

namespace List

#check foldr

-- variable {A : C} [HasInitial (Algebra (LP A))]

def foldr {A : C} [HasInitial (Algebra (LP A))]
    {S : C} (s : A ⨯ S ⟶ S) (s₀ : ⊤_ C ⟶ β) : List A ⟶ S :=
  sorry


end List



-- less organazied stuff
#synth LargeCategory (FintypeCat)

def 𝔽 := { α : Type u // Finite α }

instance : LargeCategory 𝔽 where
  Hom := fun X Y => (X.1 → Y.1)
  id {X} := id
  comp {X Y Z} f g := g ∘ f

def exceptTypeFunctor (ε : Type u) : Type v ⥤ Type (max u v) where
  obj X := Except ε X
  map {X Y} f x := match x with
  | Except.error e => Except.error e
  | Except.ok x => Except.ok (f x)

-- def exceptMonad (ε : Type u) : Monad (exceptFunctor ε) :=

variable {C : Type (u + 1)} [LargeCategory C] [HasBinaryCoproducts C]

def exceptFunctor (ε : C) : C ⥤ C where
  obj X := ε ⨿ X -- sum type for the two constructors
  map {X Y} f := coprod.map (𝟙 ε) f

local notation "𝔼" => exceptFunctor
section
variable (ε : C) (X Y : C)
#check (𝔼 ε).obj X
#reduce (𝔼 ε).obj X
end


def andThenType (attempt : Except e α) (next : α → Except e β) : Except e β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x => next x


def andThenType' (next : α → Except e β) : Except e α → Except e β :=
  fun attempt =>
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x => next x

/-
CategoryTheory.Limits.coprod.desc'.{v, u} {C : Type u} [Category.{v, u} C] {W X Y : C} [HasBinaryCoproduct X Y]
  (f : X ⟶ W) (g : Y ⟶ W) : { l // coprod.inl ≫ l = f ∧ coprod.inr ≫ l = g }
-/
#check coprod.desc'
/-
CategoryTheory.Limits.coprod.desc.{v, u} {C : Type u} [Category.{v, u} C] {W X Y : C} [HasBinaryCoproduct X Y]
  (f : X ⟶ W) (g : Y ⟶ W) : X ⨿ Y ⟶ W
-/
#check coprod.desc
-- one idea is to use concrete categories where morphisms are coerced to functions.
def andThen (ε : C) (α β : C) (next : α ⟶ (𝔼 ε).obj β) : (𝔼 ε).obj α ⟶ (𝔼 ε).obj β :=
coprod.desc (coprod.inl) next

#check List


-- the idea is to use polynomials to express the functor
-- X ↦ 1 + X + X^2 + X^3 + ...
-- extra assumptions on C
def catList : C ⥤ C := sorry

-- List A in the initial algebra for the monad C ⥤ C which takes an object `S : C` to `1 + A × S`.
-- the corresponding diagram





-- a different approach: define the list object `List A` as the initial algebra for the monad `X ↦ 1 + A × X`


def listMonad [HasTerminal C] [HasBinaryProducts C] [HasBinaryCoproducts C] (A : C) : C ⥤ C where
  obj X := (⊤_ C)  ⨿ (A ⨯ X)
  map {X Y} f := coprod.map




def firstThird' (xs : List α) : Except String (α × α) :=
  andThen (get xs 0) fun first  =>
  andThen (get xs 2) fun third =>
  Except.ok (first, third)




end CategoryTheory
