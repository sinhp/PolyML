import PolyML.Monoidal.BagInType
import PolyML.Monoidal.DSL

universe u v

namespace CategoryTheory

open Category Opposite MonoidalCategory Limits list NNO

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [ListArithmetic C] [WithBags C]

section ConcreteEvalNumbers

abbrev C_concrete := Type

noncomputable instance : WithBags C_concrete := bagType.withBags

-- Define a concrete type for our elements.
abbrev Element_c := Nat

-- Add a ToString instance for bag Element_c
noncomputable instance : ToString (bag Element_c) := by
  unfold Element_c
  exact ⟨fun b =>
    -- Step 1: Use the equivalence to convert the `bag` into a standard `Multiset`.
    let m : Multiset Element_c := (CategoryTheory.bagType.equivMultiset Element_c) b
    let counts := m.toList.map (fun elem => (elem, m.count elem)) |>.toFinset.toList
    let strings := counts.map (fun (elem, count) => s!"{count}.{elem}")
    String.intercalate " " strings⟩

noncomputable instance : Repr (bag Element_c) := by
  unfold Element_c
  refine {
    reprPrec := fun b prec => Std.Format.text (toString b)
  }

def my_concrete_list₁ : List Element_c := [2, 3, 4, 5, 2, 1, 2]

def get_list_morph : (𝟙_ C_concrete) ⟶ list Element_c :=
  fun _ => (my_concrete_list₁, PUnit.unit)

def list_prog : ListDSL (𝟙_ C_concrete) Element_c :=
  .ofMorph get_list_morph

def frequency_count_program₁ : Algorithm (𝟙_ C_concrete) Element_c (bag Element_c) :=
  .freqCount list_prog

noncomputable def frequency_count_executable_morphism₁ : (𝟙_ C_concrete) ⟶ bag Element_c :=
  frequency_count_program₁.eval

#eval! frequency_count_executable_morphism₁ PUnit.unit

end ConcreteEvalNumbers

end CategoryTheory
