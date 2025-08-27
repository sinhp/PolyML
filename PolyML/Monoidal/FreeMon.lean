/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monad.Adjunction
import PolyML.Monoidal.NNO

/-!
# Free Monoid Monad

In this file, we prove that in a list-arithmetic category, the list object `list A` is a free monoid on the object `A`.

This provides a left adjoint to the forgetful functor from `Mon_ C` to `C`.

The development here is a categorification of `Mathlib.Algebra.FreeMonoid.Basic` for types.
-/


namespace CategoryTheory

open Category CategoryTheory ListArithmetic MonoidalCategory Mon_Class NNO

universe v u

variable (C : Type u) [Category.{v} C]


/-- The free monoid functor given by the list objects of a list-arithmetic category. -/
@[simps]
def freeMon [MonoidalCategory C] [ListArithmetic C] : C ⥤ Mon_ C where
  obj A := Mon_.mk (list A)
  map {X Y} f := Mon_.Hom.mk' (list.map f) (list.map_nil) (list.append_map)
  map_id := by aesop
  map_comp := by aesop

/-- Extends the isomorphism `listUnitIsoNNO` of the types to the monoids. -/
def freeMonUnitIsoMonNNO [MonoidalCategory C] [BraidedCategory C] [ListArithmetic C] :
    (freeMon C).obj (𝟙_ C) ≅ Mon_.mk N := by
  refine Mon_.mkIso (listUnitIsoNNO C) ?_ ?_
  · simp [listUnitIsoNNO]
    aesop
  · simp [listUnitIsoNNO]
    sorry

namespace list

variable {C} [MonoidalCategory C] [ListArithmetic C]

/-- Given a monoid object `M` in `C`, we define a morphism from `list X` to `M.X` by folding the list with the multiplication of the monoid. -/
def lift {X : C} {M : Mon_ C} (f : X ⟶ M.X) : list X ⟶ M.X :=
  list.foldr ((f ▷ M.X) ≫ μ[M.X]) η[M.X]

theorem lift_one {X : C} {M : Mon_ C} {f : X ⟶ M.X} :
    η ≫ list.lift f = η := by
  dsimp [lift, list.foldr, Mon_Class.one, list.nil]
  rw [plist.nil_rec]

theorem lift_mul {X : C} {M : Mon_ C} {f : X ⟶ M.X} :
    μ ≫ list.lift f = (list.lift f ⊗ₘ list.lift f) ≫ μ :=
  sorry

/-- The underlying functor of the list monad. -/
def functor : C ⥤ C := freeMon C ⋙ Mon_.forget C

theorem functor_obj (A : C) : functor.obj A = list A := by
  rfl

theorem functor_map {A B : C} (f : A ⟶ B) : functor.map f = list.map f := by
  rfl

/-- The adjoint transposition equivalence of the hom-sets. -/
def homEquiv (X : C) (M : Mon_ C) : ((freeMon C).obj X ⟶ M) ≃ (X ⟶ (Mon_.forget C).obj M) where
  toFun f := list.singleton ≫ f.hom
  invFun f := Mon_.Hom.mk' (list.lift f) list.lift_one list.lift_mul
  left_inv f := by
    refine Mon_.Hom.ext' ?_
    simp only [freeMon_obj_X]
    dsimp [lift,foldr]
    rw [← plist.rec_uniq]
    · dsimp [list]
      sorry
    · sorry
  right_inv f := sorry

/-- `list A` is a free monoid on the object `A` witnessed by the left adjoint of the forgetful functor from `Mon_ C` to `C`. -/
def freeMonForgetAdjunction : freeMon C ⊣ Mon_.forget C :=
  Adjunction.mkOfHomEquiv {
    homEquiv (X : C) (Y : Mon_ C) := homEquiv X Y
    homEquiv_naturality_left_symm := by
      intros X X' M g h
      simp only [Mon_.forget_obj]
      dsimp [homEquiv, Mon_.Hom.mk', freeMon, Mon_.Hom.mk']
      congr
      dsimp [list.lift]
      dsimp [list.foldr]
      rw [← plist.rec_uniq]
      · dsimp [list.map, plist.map]
        simp only [← assoc, plist.nil_rec]
      · dsimp [list.map, plist.map]
        rw [← assoc, plist.cons_rec, assoc, assoc, plist.cons_rec]
        simp only [whiskerLeft_comp, assoc]
        refine _ ≫= ?_
        rw [comp_whiskerRight, assoc, ← assoc, ← assoc _ (g ▷ M.X) (h ▷ M.X ≫ _)]
        refine ?_ =≫ _
        sorry
    homEquiv_naturality_right f g := by
      dsimp [homEquiv]; rw [assoc]}

variable (C)

def monad : Monad C :=
  freeMonForgetAdjunction |> Adjunction.toMonad

variable {C}

def join {A : C} : list (list A) ⟶ list A := (monad C).μ.app A

theorem join_nil {A : C} : list.nil ≫ list.join = list.nil (C:=C) (A:=A)  := by
  dsimp [list.join, monad, freeMonForgetAdjunction, homEquiv, lift, list.foldr]
  simp [nil, plist.nil_rec]
  rfl

theorem flatten_nil {A : C} : list.nil ≫ list.flatten = list.nil (C:=C) (A:=A) := by
  dsimp [list.flatten]
  dsimp [list.rec]
  dsimp [list,list.nil]
  simp only [plist.nil_rec]

--flatten (xs:xss) = xs ++ flatten xss
theorem flatten_cons {A : C} :
  list.cons ≫ list.flatten = (list A ◁ list.flatten (A:=A)) ≫ list.append (A:=A) := by
  dsimp [list.flatten]
  dsimp [list.rec]
  dsimp [list.cons]
  rw [plist.cons_rec]

theorem join_cons {A : C} :
  list.cons ≫ list.join = list A ◁ list.join (A:=A) ≫ list.append := sorry

theorem join_eq_flatten {A : C} : list.join (A := A) = list.flatten := sorry
namespace algebra

open Category

/-- A monoid structure on `A` gives rise to an algebra for the `list` monad. -/
def ofMon (M : Mon_ C) : Monad.Algebra (monad C) where
  A := M.X
  a := lift (𝟙 _)
  unit := by
    dsimp [monad, freeMonForgetAdjunction, homEquiv, lift, list.foldr]
    simp only [comp_id]
    dsimp [list.singleton]
    rw [assoc, assoc]
    dsimp [list.cons]
    rw [plist.cons_rec]
    dsimp [list.nil]
    sorry
  assoc := by
    dsimp [monad, freeMonForgetAdjunction, homEquiv, list.foldl]
    sorry

end algebra

open algebra

def aggregator (M : Mon_ C) : list M.X ⟶ M.X :=
  (ofMon M).a

theorem aggregator_one {M : Mon_ C} : η ≫ aggregator M = η := lift_one

theorem aggregator_mul {M : Mon_ C} :
  μ ≫ aggregator M = (aggregator M ⊗ₘ aggregator M) ≫ μ := lift_mul

theorem aggregator_singleton {M : Mon_ C} :
    list.singleton ≫ aggregator M = 𝟙 M.X := by
  dsimp [aggregator, ofMon, list.singleton]
  simp only [assoc]
  dsimp [lift, list.foldr, list.cons]
  rw [plist.cons_rec]
  dsimp [list.nil]
  sorry

theorem aggregator_join {M : Mon_ C} :
  list.join ≫ aggregator M = (list.map <| aggregator M) ≫ aggregator M := by sorry

/-- Theorem: Aggregator is functorial. -/
theorem aggregator_map {M : Mon_ C} {f : M.X ⟶ M'.X} :
  list.map f ≫ aggregator M' = aggregator M ≫ f := by sorry

end list

end CategoryTheory
