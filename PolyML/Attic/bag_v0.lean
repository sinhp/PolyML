import PolyML.ListArithmetic
-- import Mathlib

universe u v

noncomputable section
namespace CategoryTheory

open Functor Opposite Limits MonoidalCategory CartesianMonoidalCategory Recursive ListArithmetic

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

open Endofunctor Algebra

variable (U : C)

structure Bag where
  /-- the base object of the bag where the elements of the bag are taken from. -/
  M : C
  /-- the fibre counts the multiplicity of the elements in the bag -/
  mult : M ⟶ U

namespace bag

def hom {M₁ M₂ : Bag U } := M₁.M ⟶ M₂.M

variable [Recursive C] [ListArithmetic C]

def lt : N_ C ⊗ N_ C ⟶ N_ C := sorry -- ⟦x < y ↔ lt x y = succ n for some n⟧.

-- we are defining the object `Fin n`. The idea is to use `Fin n` to define finiteness. An object is finite in `C` is there is an isomorphism between it and  `Fin n`.


def true : 𝟙_ C ⟶ N_ C := nno.zero ≫ nno.succ


variable [HasPullback (C:= C) true lt]

variable (C)

-- the object of pairs of elements of nno where the first coordinate is less than the seocnd
def N' := pullback (C:= C) true lt

def forget : N' C ⟶ N_ C ⊗ N_ C := pullback.snd true lt

theorem forget_mono : Mono (forget (C:= C)) := by
  sorry

variable [∀ (n : 𝟙_ C ⟶ N_ C), HasPullback (N_ C ◁ n) (forget C)]

variable {C}

def fin (n : 𝟙_ C ⟶ N_ C) := pullback (N_ C ◁ n) (forget C)

def fin.forget (n : 𝟙_ C ⟶ N_ C) : fin n ⟶ N_ C := sorry

theorem fin.forget_mono (n : 𝟙_ C ⟶ N_ C) : Mono (fin.forget (n : 𝟙_ C ⟶ N_ C)) := by
  sorry

def IsFinite (X : C) := ∃ (n : 𝟙_ C ⟶ N_ C), ∃ f : X ⟶ fin n, IsIso f

structure finBag where
    (M : C)
    mult : M ⟶ U
    has_pullback : ∀ (u : 𝟙_ C ⟶ U), HasPullback u mult := by infer_instance
    finite_fibre : ∀ (u : 𝟙_ C ⟶ U), IsFinite (pullback u mult)

-- TODO: show bag and finite bag is monad.

def finBag.join : finBag (finBag U) ⟶ finBag U := sorry

open MeasureTheory


#check Measure
#check Measurable

#check Int

#check ZNum

#check Int.instNegInt

#moogle "the type of negative integers."

#check negint

#check LaurentSeries

end bag
