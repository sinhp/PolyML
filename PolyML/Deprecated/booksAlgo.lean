import PolyML.Monoidal.DSL
import PolyML.Monoidal.BagInType

universe u v

namespace CategoryTheory

open Category Opposite MonoidalCategory Limits list NNO

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [ListArithmetic C] [WithBags C]


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

abbrev Author_c := String
abbrev Book_c   := String
abbrev Title_c  := String

def concrete_authors : List Author_c := ["A", "B", "B"]

def concrete_get_books : Author_c → List Book_c
  | "A" => ["Category Theory in Lean", "Metaprogramming Fun"]
  | "B" => ["Category Theory in Lean", "Functional Programming"]
  | _          => []

abbrev C_concrete := Type

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
end ConcreteEval
end CategoryTheory
