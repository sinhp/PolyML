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

-- Add a ToString instance for bag Element_c
noncomputable instance : ToString (bag Nat) := by
  exact ⟨fun b =>
    -- Step 1: Use the equivalence to convert the `bag` into a standard `Multiset`.
    let m : Multiset Nat := (CategoryTheory.bagType.equivMultiset Nat) b
    let counts := m.toList.map (fun elem => (elem, m.count elem)) |>.toFinset.toList
    let strings := counts.map (fun (elem, count) => s!"{count}.{elem}")
    String.intercalate " " strings⟩

noncomputable instance : Repr (bag Nat) := by
  refine {
    reprPrec := fun b prec => Std.Format.text (toString b)
  }

def my_concrete_list₁ : List Nat := [2, 3, 4, 5, 2, 1, 2]

def get_list_morph : (𝟙_ C_concrete) ⟶ list Nat :=
  fun _ => (my_concrete_list₁, PUnit.unit)

def list_prog : ListDSL (𝟙_ C_concrete) Nat :=
  .ofMorph get_list_morph

def frequency_count_program₁ : Algorithm (𝟙_ C_concrete) Nat (bag Nat) :=
  .freqCount list_prog

noncomputable def frequency_count_executable_morphism₁ :
    (𝟙_ C_concrete) ⟶ bag Nat :=
  frequency_count_program₁.eval

#eval! frequency_count_executable_morphism₁ PUnit.unit

end ConcreteEvalNumbers

end CategoryTheory
