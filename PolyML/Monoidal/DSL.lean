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
  | foldl {A B : C} (f : A ⊗ B ⟶ A) (initial : 𝟙_ C ⟶ A) (prog : ListDSL P B) : ListDSL P A


mutual
/-- `ListDSL.eval'` : `k` represents "the rest of the computation" to be composed
after the current program step is evaluated

`ListDSL.eval` : The main eval function now just kicks off the tail-recursive helper.
The initial continuation is the identity morphism, as there's no "rest of the
computation" to perform yet.
-/
  def ListDSL.eval' {P A B : C} (prog : ListDSL P A) (k : list A ⟶ B) : P ⟶ B :=
    match prog with
    | .ofMorph f => f ≫ k
    | .singleton f => f ≫ list.singleton ≫ k
    | .map f inner_prog => inner_prog.eval' (list.map f ≫ k)
    | .flatten inner_prog => inner_prog.eval' (list.flatten ≫ k)
    | .foldl f initial inner_prog =>
        let folder_morph  := list.foldl f initial
        let list_prog_eval := inner_prog.eval
        list_prog_eval ≫ folder_morph ≫ list.singleton ≫ k

  def ListDSL.eval {P A : C} (prog : ListDSL P A) : (P ⟶ list A) :=
    prog.eval' (𝟙 (list A))
end

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

--example
-- like let myList = [2, 2, 3, 4]`.
variable (my_list_morphism : 𝟙_ C ⟶ list N_as_obj)

def frequency_count_program : Algorithm (𝟙_ C) N_as_obj (bag N_as_obj) :=
  let list_prog : ListDSL (𝟙_ C) N_as_obj :=
    .ofMorph my_list_morphism
  .freqCount list_prog

def frequency_count_executable_morphism : 𝟙_ C ⟶ bag N_as_obj :=
  (frequency_count_program N_as_obj my_list_morphism).eval

end CategoryTheory
