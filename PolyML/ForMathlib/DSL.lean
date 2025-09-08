import PolyML.Monoidal.ListArithmetic
import PolyML.Monoidal.NNO
import PolyML.Monoidal.FreeMon
import PolyML.Monoidal.FreeCommMon

universe u v

namespace CategoryTheory

open Category Opposite MonoidalCategory Limits list NNO

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [ListArithmetic C] [WithBags C]


inductive ListDSL (P : C) : C → Type _ where
  | ofMorph (f : P ⟶ list A) : ListDSL P A
  | singleton (f : P ⟶ A) : ListDSL P A
  | map (f : A ⟶ B) (prog : ListDSL P A) : ListDSL P B
  | flatten (prog : ListDSL P (list A)) : ListDSL P A

-- The `ListDSL` interpreter (compiler)
def ListDSL.eval {P A : C} : ListDSL P A → (P ⟶ list A)
  | .ofMorph f => f
  | .singleton f => f ≫ list.singleton
  | .map f prog => prog.eval ≫ list.map f
  | .flatten prog => prog.eval ≫ list.flatten (A:=A)


/-!
## Step 2: The Top-Level Algorithm DSL

This DSL specifies the high-level goal. A program can either just produce a
list, or it can produce a list and then perform a frequency count on it,
resulting in a `bag`.
-/
inductive Algorithm (P : C) (A : C) : C → Type _ where
  | buildList (prog : ListDSL P A) : Algorithm P A (list A)
  | freqCount (prog : ListDSL P A) : Algorithm P A (bag A)

-- The `Algorithm` interpreter (compiler)
def Algorithm.eval {P A Out : C} : Algorithm P A Out → (P ⟶ Out)
  | .buildList prog => prog.eval
  | .freqCount prog => prog.eval ≫ bag.ofList -- The core of the solution!


-- We'll use the Natural Number Object `N` to represent the numbers in the list.
variable (N_as_obj : C) [h_nno : NNO C] (h_eq : N_as_obj = N)

-- We assume we have a process that gives us our input list.
-- This is the categorical equivalent of `let myList = [2, 2, 3, 4]`.
variable (my_list_morphism : 𝟙_ C ⟶ list N_as_obj)


-- The algorithm, written in our high-level DSL.
def frequency_count_program : Algorithm (𝟙_ C) N_as_obj (bag N_as_obj) :=

  -- First, we specify the input list using the `ListDSL`.
  let list_prog : ListDSL (𝟙_ C) N_as_obj :=
    .ofMorph my_list_morphism

  -- Then, we use the top-level `Algorithm` DSL to say:
  -- "take this list program and perform a frequency count on its result."
  .freqCount list_prog


-- To get the final, executable morphism, we "compile" our DSL program.
def frequency_count_executable_morphism : 𝟙_ C ⟶ bag N_as_obj :=
  (frequency_count_program N_as_obj my_list_morphism).eval

/-!
### How It Works

The magic happens in the `Algorithm.eval` function for the `.freqCount` case:

`| .freqCount prog => prog.eval ≫ bag.ofList`

1.  `prog.eval`: The interpreter first calls `ListDSL.eval` on the inner program (`list_prog`). This produces the morphism that generates the input list, in our case, `my_list_morphism`.
2.  `≫ bag.ofList`: It then **composes** this result with `bag.ofList`. This is the powerful morphism from your API that takes a `list A` and correctly converts it into a `bag A` by collecting and counting identical elements.

The final compiled program is the single morphism `my_list_morphism ≫ bag.ofList`.

Your DSL successfully abstracts away the details of morphism composition, allowing you to state your high-level intent ("I want to count the elements") which is then compiled down to the precise, correct categorical implementation.
-/


/-!
## Step 4: A More Complex Evaluation Example

Let's implement a more involved algorithm: "Given a list of authors, find all their
books, get the title of each book, and then count the frequency of each title."

This demonstrates a chain of `map` and `flatten` (a monadic bind) before the
final `freqCount`.
-/

-- Define the objects and morphisms for our new "world".
variable (Author Book Title : C)
variable (get_authors : 𝟙_ C ⟶ list Author)
variable (get_books : Author ⟶ list Book) -- Each author has a list of books
variable (get_title : Book ⟶ Title)

-- The algorithm for counting book title frequencies, written in the DSL.
def book_title_frequency_program : Algorithm (𝟙_ C) Title (bag Title) :=

  -- First, we build the program to get a flat list of all book titles.
  let titles_prog : ListDSL (𝟙_ C) Title :=

    -- Start with the initial list of authors.
    let authors_prog : ListDSL (𝟙_ C) Author :=
      .ofMorph get_authors

    -- For each author, get their list of books. This results in a nested list
    -- of books: `list (list Book)`.
    let nested_books_prog : ListDSL (𝟙_ C) (list Book) :=
      .map get_books authors_prog

    -- Flatten the nested list to get a single list of all books: `list Book`.
    let books_prog : ListDSL (𝟙_ C) Book :=
      .flatten nested_books_prog

    -- Map over the final list of books to get their titles: `list Title`.
    .map get_title books_prog

  -- Finally, use the top-level Algorithm DSL to count the frequencies.
  .freqCount titles_prog

-- "Compiling" this complex program into a single, executable morphism.
def book_title_frequency_executable_morphism : 𝟙_ C ⟶ bag Title :=
  (book_title_frequency_program Author Book Title get_authors get_books get_title).eval

/-!
## Step 5: Concrete Evaluation with #eval

To demonstrate a concrete execution, we specialize our category `C` to `Type`,
where morphisms are functions, `list` is `List`, and `bag` represents a multiset.
-/
section ConcreteEval

-- Let's explicitly set our category to `Type` to resolve universe issues.
abbrev C_concrete := Type u

-- 1. Define concrete types for our book example.
abbrev Author_c := String
abbrev Book_c   := String
abbrev Title_c  := String

-- 2. Define concrete data and functions (morphisms in `Type`).
def concrete_authors : List Author_c := ["Sina H.", "David S."]

def concrete_get_books : Author_c → List Book_c
  | "Sina H." => ["Category Theory in Lean", "Metaprogramming Fun"]
  | "David S." => ["Category Theory in Lean", "Functional Programming"]
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

#eval (concrete_titles_morphism PUnit.unit).1

-- def concrete_freq_count_program : Algorithm (𝟙_ C_concrete) Title_c (bag Title_c) :=
--   .freqCount concrete_titles_prog

-- def concrete_freq_count_morphism := (concrete_freq_count_program).eval

--#check concrete_freq_count_morphism

end ConcreteEval
