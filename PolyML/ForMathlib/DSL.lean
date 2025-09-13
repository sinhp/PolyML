import PolyML.Monoidal.ListArithmetic
import PolyML.Monoidal.NNO
import PolyML.Monoidal.FreeMon
import PolyML.Monoidal.FreeCommMon

universe u v

namespace CategoryTheory

open Category Opposite MonoidalCategory Limits list NNO

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [ListArithmetic C] [WithBags C]


/-an interpreter-/
inductive ListDSL (P : C) : C → Type _ where
  | ofMorph (f : P ⟶ list A) : ListDSL P A
  | singleton (f : P ⟶ A) : ListDSL P A
  | map (f : A ⟶ B) (prog : ListDSL P A) : ListDSL P B
  | flatten (prog : ListDSL P (list A)) : ListDSL P A

/-- `k` represents "the rest of the computation" to be composed
after the current program step is evaluated
-/
def ListDSL.eval' {P A B : C} (prog : ListDSL P A) (k : list A ⟶ B) : P ⟶ B :=
  match prog with
  | .ofMorph f => f ≫ k
  | .singleton f => f ≫ list.singleton ≫ k
  | .map f inner_prog => inner_prog.eval' (list.map f ≫ k)
  | .flatten inner_prog => inner_prog.eval' (list.flatten ≫ k)

/--
The main eval function now just kicks off the tail-recursive helper.
The initial continuation is the identity morphism, as there's no "rest of the
computation" to perform yet.
-/
def ListDSL.eval {P A : C} (prog : ListDSL P A) : (P ⟶ list A) :=
  prog.eval' (𝟙 (list A))

/-!
A program can either just produce a list, or it can produce a list
and then perform a frequency count on it, resulting in a `bag`.
-/
inductive Algorithm (P : C) (A : C) : C → Type _ where
  | buildList (prog : ListDSL P A) : Algorithm P A (list A)
  | freqCount (prog : ListDSL P A) : Algorithm P A (bag A)

-- The `Algorithm` interpreter (compiler)
def Algorithm.eval {P A Out : C} : Algorithm P A Out → (P ⟶ Out)
  | .buildList prog => prog.eval
  | .freqCount prog => prog.eval ≫ bag.ofList -- The core of the solution!

-- we use the nno `N` to represent the numbers in the list
variable (N_as_obj : C) [h_nno : NNO C] (h_eq : N_as_obj = N)

-- like let myList = [2, 2, 3, 4]`.
variable (my_list_morphism : 𝟙_ C ⟶ list N_as_obj)

def frequency_count_program : Algorithm (𝟙_ C) N_as_obj (bag N_as_obj) :=
  let list_prog : ListDSL (𝟙_ C) N_as_obj :=
    .ofMorph my_list_morphism
  .freqCount list_prog

def frequency_count_executable_morphism : 𝟙_ C ⟶ bag N_as_obj :=
  (frequency_count_program N_as_obj my_list_morphism).eval


/-!
Given a list of authors, find all their
books, get the title of each book, and then count the frequency of each title"
-/

variable (Author Book Title : C)
variable (get_authors : 𝟙_ C ⟶ list Author)
variable (get_books : Author ⟶ list Book)
variable (get_title : Book ⟶ Title)

def book_title_frequency_program : Algorithm (𝟙_ C) Title (bag Title) :=
  let titles_prog : ListDSL (𝟙_ C) Title :=
    let authors_prog : ListDSL (𝟙_ C) Author :=
      .ofMorph get_authors
    let nested_books_prog : ListDSL (𝟙_ C) (list Book) :=
      .map get_books authors_prog
    let books_prog : ListDSL (𝟙_ C) Book :=
      .flatten nested_books_prog
    .map get_title books_prog
  .freqCount titles_prog

def book_title_frequency_executable_morphism : 𝟙_ C ⟶ bag Title :=
  (book_title_frequency_program Author Book Title get_authors get_books get_title).eval

section ConcreteEval

abbrev C_concrete := Type u

abbrev Author_c := String
abbrev Book_c   := String
abbrev Title_c  := String

def concrete_authors : List Author_c := ["A", "B", "B"]

def concrete_get_books : Author_c → List Book_c
  | "A" => ["Category Theory in Lean", "Metaprogramming Fun"]
  | "B" => ["Category Theory in Lean", "Functional Programming"]
  | _          => []

def concrete_get_title (book : Book_c) : Title_c := book

def get_authors_morph : 𝟙_ C_concrete ⟶ list Author_c := fun _ => (concrete_authors, PUnit.unit)
def get_books_morph : Author_c ⟶ list Book_c := fun author => (concrete_get_books author, PUnit.unit)
def get_title_morph : Book_c ⟶ Title_c := concrete_get_title

def concrete_titles_prog : ListDSL (𝟙_ C_concrete) Title_c :=
  let authors_prog      := ListDSL.ofMorph get_authors_morph
  let nested_books_prog := ListDSL.map get_books_morph authors_prog
  let books_prog        := ListDSL.flatten nested_books_prog
  .map get_title_morph books_prog

def concrete_titles_morphism := (concrete_titles_prog).eval

#eval (concrete_titles_morphism PUnit.unit)

-- We switch to a concrete category to run the algorithm
section ConcreteEvalNumbers

-- Let our category `C` be the category of types, `Type`.
abbrev C_concrete₁ := Type

instance : WithBags C_concrete₁ := sorry

-- Define a concrete type for our elements.
abbrev Element_c := Nat

-- Add a Repr instance for bag Element_c to enable #eval
instance : Repr (bag Element_c) := by {
  unfold Element_c

}

def my_concrete_list₁ : List Element_c := [2, 3, 4, 5, 2, 1, 2]

def get_list_morph : (𝟙_ C_concrete₁) ⟶ list Element_c :=
  fun _ => (my_concrete_list₁, PUnit.unit)

def list_prog : ListDSL (𝟙_ C_concrete) Element_c :=
  .ofMorph get_list_morph

def frequency_count_program₁ : Algorithm (𝟙_ C_concrete) Element_c (bag Element_c) :=
  .freqCount list_prog

def frequency_count_executable_morphism₁ : (𝟙_ C_concrete) ⟶ bag Element_c :=
  frequency_count_program₁.eval

-- Step 5: Run the resulting function and see the output.
-- We call the function with the only possible value for `PUnit`, which is `()`.
#eval frequency_count_executable_morphism₁ PUnit.unit

end ConcreteEvalNumbers



end ConcreteEval

end CategoryTheory
