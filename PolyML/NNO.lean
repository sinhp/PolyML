/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Monoidal.Comon_
import PolyML.ForMathlib.ConstantMorphism
import PolyML.ListArithmetic

universe u v

namespace CategoryTheory

open Category Opposite Limits MonoidalCategory CartesianMonoidalCategory

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

open Endofunctor Algebra

variable {C : Type u} [Category.{v} C]

-- SH: prec for "parameterized" recursion.
class IsNNO [MonoidalCategory C] {N : C} (zero : 𝟙_ C ⟶ N) (succ : N ⟶ N) where
  prec {A B : C} (f : A ⟶ B) (g : B ⟶ B) : N ⊗ A ⟶ B
  zero_prec {A B : C} {f : A ⟶ B} {g : B ⟶ B} : (zero ▷ A) ≫ prec f g = (λ_ A).hom ≫ f
  succ_prec {A B : C} {f : A ⟶ B} {g : B ⟶ B} : (succ ▷ A) ≫ prec f g = prec f g ≫ g
  prec_uniq {A B : C} {f : A ⟶ B} {g : B ⟶ B} (r : N ⊗ A ⟶ B)
  (h_zero : (zero ▷ A) ≫ r = (λ_ A).hom ≫ f) (h_succ: (succ ▷ A) ≫ r = r ≫ g) : r = prec f g

namespace IsNNO

variable [MonoidalCategory C]

variable {N : C} {zero : 𝟙_ C ⟶ N} {succ : N ⟶ N} [IsNNO zero succ]

theorem congr_arg {A B : C} {f f' : A ⟶ B} {g g' : B ⟶ B}
    (h : f = f') (h' : g = g') :
    prec zero succ f g = prec zero succ f' g' := by
  subst h h'
  rfl

/-- Any two natural number objects in a monoidal category are isomorphic. -/
def iso {N N' : C} {zero : 𝟙_ C ⟶ N} {succ : N ⟶ N} {zero' : 𝟙_ C ⟶ N'} {succ' : N' ⟶ N'}
    [IsNNO zero succ] [IsNNO zero' succ'] : N ≅ N' where
  hom := (ρ_ N).inv ≫ prec zero succ zero' succ'
  inv := (ρ_ N').inv ≫ prec zero' succ' zero succ
  hom_inv_id := sorry
  inv_hom_id := sorry

end IsNNO

variable (C)

/-- A natural number object in a monoidal category. -/
class NNO [MonoidalCategory C] where
  /-- The (left) natural number object. -/
  N : C
  /-- The zero morphism. -/
  zero : 𝟙_ C ⟶ N
  /-- The successor morphism. -/
  succ : N ⟶ N
  /-- The natural number object satisfies the properties of a left natural number object. -/
  [isNNO : IsNNO zero succ]

-- @[inherit_doc] notation "N_" => NNO.N

def nno (C : Type u) [Category.{v} C] [MonoidalCategory C] [NNO C] : C := NNO.N

namespace NNO

open IsNNO

variable {C} [MonoidalCategory C] [NNO C] {A B : C}

instance : IsNNO (zero : 𝟙_ C ⟶ N) (succ : N ⟶ N) :=
  NNO.isNNO

def prec (f : A ⟶ B) (g : B ⟶ B) : N ⊗ A ⟶ B :=
  IsNNO.prec zero succ f g

@[simp]
theorem zero_prec {f : A ⟶ B} {g : B ⟶ B} :
    (zero ▷ A) ≫ prec f g = (λ_ A).hom ≫ f := by
  apply IsNNO.zero_prec

theorem succ_prec {f : A ⟶ B} {g : B ⟶ B} :
    (succ ▷ A) ≫ prec f g = prec f g ≫ g := by
  apply IsNNO.succ_prec

theorem prec_precompose {A'} {u : A' ⟶ A} {f : A ⟶ B} {g : B ⟶ B} :
    N ◁ u ≫ prec f g = prec (u ≫ f) g := by
  apply prec_uniq
  all_goals rw [← assoc, ← whisker_exchange, assoc]
  · rw [zero_prec]
    aesop
  · rw [succ_prec]
    aesop

/-- Iterates an endofunction a natural number of times. -/
def iter (f : A ⟶ A) : N ⊗ A ⟶ A := prec (𝟙 _) (f)

/-- Recursion with the parameter `A` set to the unit object `𝟙_ C` -/
def urec (f : 𝟙_ C ⟶ B) (g : B ⟶ B) : N ⟶ B :=
  (ρ_ _).inv ≫ prec f g

@[reassoc (attr := simp)]
theorem zero_iter {f : A ⟶ A} :
    zero ▷ A ≫ iter f = (λ_ A).hom := by
  simp [iter]

theorem succ_iter {f : A ⟶ A} :
    succ ▷ A ≫ iter f = iter f ≫ f := by
  simp [iter, succ_prec]

/-- `prec` can be reconstructed from `iter`. -/
@[reassoc (attr := simp)]
theorem iter_prec {f : A ⟶ B} {g : B ⟶ B} : (N ◁ f) ≫ iter g = prec f g := by
  simpa using prec_precompose (u:= f) (f:= 𝟙 B) (g:= g)

theorem uniq {f : A ⟶ B} {g : B ⟶ B} (r : N ⊗ A ⟶ B)
    (h_zero : (zero ▷ A) ≫ r = (λ_ A).hom ≫ f) (h_succ : (succ ▷ A) ≫ r = r ≫ g) :
    r = (N ◁ f) ≫ iter g := by
  rw [iter_prec]
  apply IsNNO.prec_uniq
  all_goals
  assumption

/-- The number one. -/
def one : 𝟙_ C ⟶ N := zero ≫ succ

/-- Addition of natural numbers. -/
def add : (N : C) ⊗ N ⟶ N := iter succ

@[reassoc (attr := simp)]
theorem zero_add : zero ▷ (N : C) ≫ add = (λ_ N).hom := by
  simp [add]

theorem succ_add : succ ▷ (N : C) ≫ add = add ≫ succ := by
  simp [add, succ_iter]

#check leftUnitor_naturality
#check rightUnitor_naturality

#moogle ""

theorem one_add_zero :
    (one ⊗ₘ zero) ≫ add = (λ_ (𝟙_ C)).hom ≫ one := by
  simp [add]
  rw [tensorHom_def_assoc]
  sorry

theorem zero_add_one : (zero ⊗ₘ one) ≫ add = (λ_ (𝟙_ C)).hom ≫ one := by
  sorry

-- commutativity of addition
theorem add_comm [BraidedCategory C] : (β_ (N : C) N).hom ≫ add = add := by
  sorry

theorem add_zero [BraidedCategory C] : (N : C) ◁ zero ≫ add = (ρ_ N).hom := by
  rw [← add_comm]
  aesop

-- associativity of addition
theorem add_assoc [BraidedCategory C] :
    add ▷ (N : C) ≫ add = (α_ _ _ _).hom ≫ (N ◁ add) ≫ add := by
  dsimp [add]
  sorry

/-- The monoid structure on the natural number object. -/
instance monClass [BraidedCategory C] : Mon_Class (N : C) where
  one := zero
  mul := add
  one_mul := zero_add
  mul_one := add_zero
  mul_assoc := add_assoc

instance [BraidedCategory C] : IsCommMon (N : C) where
  mul_comm := add_comm

def iterCurried [Closed A] [BraidedCategory C] (f : A ⟶ A) : N ⟶ (A ⟶[C] A) :=
  (MonoidalClosed.curry <| (β_ _ _).hom ≫ iter f)

end NNO

open NNO

/-- Every list-arithmetic category has a natural number object. -/
@[simps]
instance arithmeticOfListArithmetic [MonoidalCategory C] [ListArithmetic C] : NNO C where
  N := list (𝟙_ C)
  zero := list.nil
  succ := (λ_ _).inv ≫ list.cons (A:= 𝟙_ C)
  isNNO := {
    prec e a := list.prec e ((λ_ _).hom ≫ a)
    zero_prec := by sorry -- list.nil_prec
    succ_prec {A B f g}:= by
      rw [comp_whiskerRight, assoc]
      rw [list.cons_prec]
      sorry
    prec_uniq := by sorry --simp [list.prec_uniq]
  }

namespace list

variable {C} [MonoidalCategory C] [ListArithmetic C]

/-- The length of a list. -/
def len (isTerminalTensorUnit : IsTerminal (𝟙_ C) := by aesop) {A : C} : list A ⟶ N :=
  list.map <| isTerminalTensorUnit.from A

namespace length

variable (h : IsTerminal (𝟙_ C))

variable {A : C}

theorem cons_len_eq_map_toUnit_cons {A : C} : list.cons ≫ list.len h =
    A ◁ list.map (toUnit h A) ≫ (toUnit h A ▷ list (𝟙_ C)) ≫ list.cons (A := 𝟙_ C) := by
  dsimp [list.len, list.cons, list.map]
  rw [plist.cons_map]
  rfl

@[reassoc (attr := simp)]
theorem nil_len_zero : list.nil (A:= A) ≫ list.len = zero := by
  simp [len]
  rfl

-- len (a :: xs) = succ (len xs)
theorem cons_len_succ :
    list.cons ≫ list.len = (toUnit h A ⊗ₘ list.len) ≫ (λ_ N).hom ≫ succ := by
  dsimp [list.len]
  rw [list.cons_map]
  rw [← Category.assoc]
  rw [tensorHom_def']
  congr 1
  simp_all only [Iso.hom_inv_id_assoc]

set_option diagnostics true

-- --len (cons x xs) = succ (len xs)
-- lemma len_cons [CartesianMonoidalCategory C] [HasBinaryCoproducts C] [ListArithmetic C] :
--   list.cons ≫ list.len = list.tail ≫ list.len (C:=C) ≫ succ := by {
--   dsimp [list.len', list.rec', list.cons]
--   rw [plist.rec_cons]
--   simp only [whiskerLeft_snd_assoc]
--   dsimp [list.tail, list]}

set_option diagnostics true
-- len ([x]) = 1
theorem singleton_len_one :
    list.singleton ≫ list.len = toUnit h A ≫ one := by
  dsimp [len, singleton, one]
  rw [assoc, assoc]
  rw [cons_map]
  rw [← assoc, ← assoc, ← assoc, ← assoc, ← assoc]
  refine ?_ =≫ cons
  dsimp [map]
  rw [assoc, assoc]
  have : (ρ_ A).inv ≫ A ◁ nil ≫ A ◁ plist.map (h.from A) ≫ h.from A ▷ list (𝟙_ C)=
  (ρ_ A).inv ≫ (A ◁ nil ≫ A ◁ plist.map (h.from A)) ≫ h.from A ▷ list (𝟙_ C) := by {
    simp only [assoc]
  }
  rw [this]
  clear this
  dsimp [nil]
  rw [plist.whiskerLeft_nil_whiskerLeft_map]
  refine (Iso.inv_comp_eq (ρ_ A)).mpr ?_
  dsimp [MonoidalCategory.toUnit]
  rw [← assoc]
  rw [← id_comp (f:= (λ_ (list (𝟙_ C))).inv)]
  rw [← assoc]
  refine (Iso.eq_comp_inv (λ_ (list (𝟙_ C)))).mpr ?_
  rw [← MonoidalCategory.rightUnitor_naturality]
  simp only [assoc, whiskerRight_id, Iso.inv_hom_id, comp_id]
  rw [← assoc]
  refine (Iso.eq_comp_inv (λ_ (list (𝟙_ C)))).mp ?_
  rw [assoc,assoc]
  rw [MonoidalCategory.leftUnitor_inv_naturality]
  sorry


end length

end list

namespace NNO

section Comon

variable {C} [MonoidalCategory C] [NNO C]

def duplicate : (N : C) ⟶ N ⊗ N :=
  (ρ_ _).inv ≫ prec ((λ_ _).inv ≫ (zero ⊗ₘ zero)) (succ ⊗ₘ succ)

def delete : N ⟶ 𝟙_ C := (ρ_ _).inv ≫ iter (𝟙 _)

/-- The comonoid structure on the natural number object. -/
instance : Comon_Class (N : C) where
  counit := delete
  comul := duplicate
  counit_comul := by
    simp only [duplicate, delete]
    sorry
  comul_counit := by {
    simp only [duplicate]
    sorry
  }
  comul_assoc := sorry

def swap : (N : C) ⊗ N ⟶ N ⊗ N := prec ((λ_ _).inv ≫ (zero ▷ N)) (N ◁ succ)

theorem swap_swap : swap ≫ swap = 𝟙 (N ⊗ N : C) := by
  sorry

end Comon

section const

open ConstantMorphism

variable {C} [MonoidalCategory C] [ListArithmetic C] (h : IsTerminal (𝟙_ C))

/-- `∀ n, f (succ n, a) = f (n, a)` implies `∀ n, f (n, a) = f (0, a)`. -/
theorem const_of_no_change_succ {A B : C} (r : N ⊗ A ⟶ B) (no_change_succ : succ ▷ A ≫ r = r) {n} :
    r = (const h N n) ▷ A ≫ r := by
  sorry


end const

namespace PR

variable {C} [CartesianMonoidalCategory C] [ListArithmetic C]





/-- The general primitive recursion schema. -/
def pr := 2


end PR

end NNO

end CategoryTheory
