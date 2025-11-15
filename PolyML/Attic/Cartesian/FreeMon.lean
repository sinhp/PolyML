/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Algebra
import PolyML.Monoidal.ListArithmetic

/-
In this file, we prove that in a list-arithmetic category, the list object `list A` is a free monoid on the object `A`.
Our development here is a categorification of `Mathlib.Algebra.FreeMonoid.Basic` for types.
-/
namespace CategoryTheory

open Category CategoryTheory Recursive ListArithmetic Functor MonoidalCategory Mon_Class Monad

universe v u

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] [ListArithmetic C]

attribute [local instance] CartesianMonoidalCategory.toSymmetricCategory
attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory


/-- The free monoid functor given by the list objects of a list-arithmetic category. -/
@[simps]
def freeMon : C ⥤ Mon_ C where
  obj A := Mon_.mk (list A)
  map {X Y} f := Mon_.Hom.mk' (list.map f) (list.map_nil) (list.append_map)
  map_id := by aesop
  map_comp := by aesop

namespace list

variable {C}

/-- Given a monoid object `M` in `C`, we define a morphism from `list X` to `M.X` by folding the list with the multiplication of the monoid. -/
def lift {X : C} {M : Mon_ C} (f : X ⟶ M.X) : list X ⟶ M.X :=
  list.foldl ((M.X ◁ f) ≫ μ[M.X]) η[M.X]

theorem lift_one {X : C} {M : Mon_ C} {f : X ⟶ M.X} :
    η ≫ list.lift f = η := by
  dsimp [lift]
  dsimp [list.foldl]
  rw [← Category.assoc]
  dsimp [Mon_Class.one]
  dsimp [list.nil]
  rw [plist.nil_rec]

theorem lift_mul {X : C} {M : Mon_ C} {f : X ⟶ M.X} :
    μ ≫ list.lift f = (list.lift f ⊗ₘ list.lift f) ≫ μ :=
  sorry

def functor : C ⥤ C := freeMon C ⋙ Mon_.forget C

theorem functor_obj (A : C) : functor.obj A = list A := rfl

theorem functor_map {A B : C} (f : A ⟶ B) : functor.map f = list.map f := rfl

/-- The adjoint transposition equivalence of the hom-sets. -/
def homEquiv (X : C) (M : Mon_ C) : ((freeMon C).obj X ⟶ M) ≃ (X ⟶ (Mon_.forget C).obj M) where
  toFun := fun f => list.singleton ≫ f.hom
  invFun := fun f => (Mon_.Hom.mk' (list.lift f) list.lift_one list.lift_mul)
  left_inv := fun f => by {
    dsimp
    refine Mon_.Hom.ext' ?_
    simp only [freeMon_obj_X]
    dsimp [lift,foldl]
    rw [← plist.rec_uniq]
    · dsimp [list]
      sorry
    · simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      BraidedCategory.braiding_naturality_right_assoc]
      sorry
  }
  right_inv := fun f => sorry

/-- `list A` is a free monoid on the object `A` witnessed by the left adjoint of the forgetful functor from `Mon_ C` to `C`. -/
def freeMonoidAdjunction : freeMon C ⊣ Mon_.forget C :=
  Adjunction.mkOfHomEquiv {
    homEquiv (X : C) (Y : Mon_ C) := homEquiv X Y
    homEquiv_naturality_left_symm := by {
    intros X X' f g h
    simp only [Mon_.forget_obj]
    dsimp [homEquiv]
    dsimp [Mon_.Hom.mk']
    dsimp [freeMon, Mon_.Hom.mk']
    congr
    simp only
    dsimp [list.lift]
    dsimp [list.foldl]
    rw [← plist.rec_uniq]
    · dsimp [list.map, plist.map]
      rw [← Category.assoc]
      simp only [plist.nil_rec]
    · dsimp [list.map, plist.map]
      rw [← Category.assoc]
      rw [plist.cons_rec]
      rw [Category.assoc]
      letI : BraidedCategory C := CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory
      simp only [ Category.assoc]
      rw [plist.cons_rec]
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
      refine X ◁ plist.rec plist.nil (g ▷ plist X' (𝟙_ C) ≫ plist.cons) ≫= ?_
      have :  g ▷ plist X' (𝟙_ C) ≫ X' ◁ plist.rec η ((β_ X' f.X).hom ≫ f.X ◁ h ≫ μ) ≫
        (β_ X' f.X).hom ≫ f.X ◁ h ≫ μ =
        (g ▷ plist X' (𝟙_ C) ≫ X' ◁ plist.rec η ((β_ X' f.X).hom ≫ f.X ◁ h ≫ μ) ≫
         (β_ X' f.X).hom) ≫ f.X ◁ h ≫ μ := by {
          simp only [Mon_.forget_obj,BraidedCategory.braiding_naturality_right_assoc,
            BraidedCategory.braiding_naturality_left_assoc,
            BraidedCategory.braiding_naturality_right, Category.assoc]}
      rw [this]
      have :  X ◁ plist.rec η ((β_ X' f.X).hom ≫ f.X ◁ h ≫ μ) ≫
      (β_ X f.X).hom ≫ f.X ◁ g ≫ f.X ◁ h ≫ μ=
       (X ◁ plist.rec η ((β_ X' f.X).hom ≫ f.X ◁ h ≫ μ) ≫
       (β_ X f.X).hom ≫ f.X ◁ g) ≫ f.X ◁ h ≫ μ := by {
        simp only [Mon_.forget_obj, BraidedCategory.braiding_naturality_right_assoc, Category.assoc]}
      rw [this]
      refine ?_ =≫ f.X ◁ h ≫ μ
      rename_i this_1 this_2
      simp_all only [Mon_.forget_obj, BraidedCategory.braiding_naturality_right_assoc,
      BraidedCategory.braiding_naturality_left_assoc,
     BraidedCategory.braiding_naturality_right, Category.assoc,
      Iso.cancel_iso_hom_left, this_1]
      ext : 1
      · simp_all only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
        CartesianMonoidalCategory.whiskerLeft_fst_assoc, CartesianMonoidalCategory.whiskerLeft_fst]
      · simp_all only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
        CartesianMonoidalCategory.whiskerLeft_snd, CartesianMonoidalCategory.whiskerRight_snd_assoc]}
    homEquiv_naturality_right f g := by {
      dsimp [homEquiv]; rw [Category.assoc]
    }
  }

variable (C)

def monad : Monad C :=
  freeMonoidAdjunction |> Adjunction.toMonad

variable {C}

def join {A : C} : list (list A) ⟶ list A := (monad C).μ.app A

theorem join_nil {A : C} : list.nil ≫ list.join = list.nil (C:=C) (A:=A)  := by
  dsimp [list.join, monad, freeMonoidAdjunction, homEquiv, lift, list.foldl]
  simp only [MonoidalCategory.whiskerLeft_id, id_comp]
  dsimp [list,list.nil]
  simp only [plist.nil_rec]
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
def ofMon (M : Mon_ C) : Algebra (monad C) where
  A := M.X
  a := lift (𝟙 _)
  unit := by {
    dsimp [monad, freeMonoidAdjunction, homEquiv, lift, list.foldl]
    simp only [comp_id, MonoidalCategory.whiskerLeft_id, id_comp]
    dsimp [list.singleton]
    rw [Category.assoc, Category.assoc]
    dsimp [list.cons]
    rw [plist.cons_rec]
    have h1 : (ρ_ M.X).inv ≫ M.X ◁ list.nil ≫ M.X ◁ plist.rec η
     ((β_ M.X M.X).hom ≫ μ) ≫ (β_ M.X M.X).hom ≫ μ =
     (ρ_ M.X).inv ≫ (M.X ◁ list.nil ≫ M.X ◁ plist.rec η
     ((β_ M.X M.X).hom ≫ μ)) ≫ (β_ M.X M.X).hom ≫ μ := by {
      simp only [BraidedCategory.braiding_naturality_right_assoc,
        braiding_tensorUnit_right, Category.assoc, Iso.inv_hom_id_assoc]}
    rw [h1]
    nth_rw 1 [← MonoidalCategory.whiskerLeft_comp]
    dsimp [list.nil]
    rw [plist.nil_rec]
    simp only [BraidedCategory.braiding_naturality_right_assoc,
      braiding_tensorUnit_right,Mon_Class.one_mul,
      Category.assoc, Iso.inv_hom_id, comp_id]
    }
  assoc := by {
    dsimp [monad, freeMonoidAdjunction, homEquiv, list.foldl]
    sorry
  }

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
  simp only [Category.assoc]
  dsimp [lift, list.foldl, list.cons]
  rw [plist.cons_rec]
  dsimp [list.nil]
  have h1 : M.X ◁ list.nil ≫ M.X ◁ plist.rec η ((β_ M.X M.X).hom ≫ M.X ◁ 𝟙 M.X ≫ μ) =
    M.X ◁ (list.nil ≫ plist.rec η ((β_ M.X M.X).hom ≫ M.X ◁ 𝟙 M.X ≫ μ)) := by {
      simp only [MonoidalCategory.whiskerLeft_comp]}
  dsimp [list.nil] at h1
  have : (ρ_ M.X).inv ≫
    M.X ◁ plist.nil ≫ M.X ◁ plist.rec η ((β_ M.X M.X).hom ≫ M.X ◁ 𝟙 M.X ≫ μ)
    ≫ (β_ M.X M.X).hom ≫ M.X ◁ 𝟙 M.X ≫ μ =
  (ρ_ M.X).inv ≫
    (M.X ◁ plist.nil ≫ M.X ◁ plist.rec η ((β_ M.X M.X).hom ≫ M.X ◁ 𝟙 M.X ≫ μ))
    ≫ (β_ M.X M.X).hom ≫ M.X ◁ 𝟙 M.X ≫ μ := by {
      rw [Category.assoc]}
  rw [this, h1]
  simp only [MonoidalCategory.whiskerLeft_id, id_comp, plist.nil_rec,
    BraidedCategory.braiding_naturality_right_assoc,
    braiding_tensorUnit_right, Mon_Class.one_mul,
    Category.assoc, Iso.inv_hom_id, comp_id]

theorem aggregator_join {M : Mon_ C} :
  list.join ≫ aggregator M = (list.map <| aggregator M) ≫ aggregator M := by sorry

/-- Theorem: Aggregator is functorial. -/
theorem aggregator_map {M : Mon_ C} {f : M.X ⟶ M'.X} :
  list.map f ≫ aggregator M' = aggregator M ≫ f := by sorry

end list

end CategoryTheory
