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
    dsimp [Mon_Class.mul, add, iter, prec]
    apply list.prec_uniq
    · simp only [list.whiskerRight_nil_append, comp_id]
    · nth_rw 1 [list.append]
      rw [← Category.assoc, list.cons_prec]
      simp only [id_whiskerLeft, Category.assoc, Iso.hom_inv_id_assoc, Iso.cancel_iso_hom_left]
      dsimp [list.append]

namespace list

variable {C} [MonoidalCategory C] [ListArithmetic C]

/-- Given a monoid object `M` in `C`, we define a morphism from `list X` to `M.X` by folding the list with the multiplication of the monoid. -/
def lift {X : C} {M : Mon_ C} (f : X ⟶ M.X) : list X ⟶ M.X :=
  list.foldr ((f ▷ M.X) ≫ μ[M.X]) η[M.X]

theorem lift_one {X : C} {M : Mon_ C} {f : X ⟶ M.X} :
    η ≫ list.lift f = η := by
  dsimp [lift, list.foldr, Mon_Class.one, list.nil]
  rw [plist.nil_rec]

theorem lift_one_whiskerRight {M : Mon_ C} {f : X ⟶ M.X} {Y : C} :
  (η ▷ X) ≫ (list.lift f ▷ X) = η ▷ X := by
  dsimp [lift, list.foldr, Mon_Class.one, list.nil]
  apply plist.whiskerRight_nil_whiskerRight_rec

theorem lift_mul {X : C} {M : Mon_ C} {f : X ⟶ M.X} :
    μ ≫ list.lift f = (list.lift f ⊗ₘ list.lift f) ≫ μ := by
  rw [tensorHom_def_assoc]
  dsimp [Mon_Class.mul]
  dsimp [append]
  sorry

/-- The underlying functor of the list monad. -/
def functor : C ⥤ C := freeMon C ⋙ Mon_.forget C

theorem functor_obj (A : C) : functor.obj A = list A := by
  rfl

theorem functor_map {A B : C} (f : A ⟶ B) : functor.map f = list.map f := by
  rfl

/-- The adjoint transposition equivalence of the hom-sets. -/
def homEquiv (X : C) (M : Mon_ C) : ((freeMon C).obj X ⟶ M) ≃ (X ⟶ (Mon_.forget C).obj M) where
  toFun := fun f => list.singleton ≫ f.hom
  invFun := fun f => (Mon_.Hom.mk' (list.lift f) list.lift_one list.lift_mul)
  left_inv := fun f => sorry
  right_inv := fun f => by sorry

/-- `list A` is a free monoid on the object `A` witnessed by the left adjoint of the forgetful functor from `Mon_ C` to `C`. -/
def freeMonForgetAdjunction : freeMon C ⊣ Mon_.forget C :=
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
    dsimp [list.foldr]
    rw [← plist.rec_uniq]
    · dsimp [list.map, plist.map]
      rw [← Category.assoc]
      simp only [plist.nil_rec]
    · dsimp [list.map, plist.map]
      rw [← Category.assoc]
      rw [plist.cons_rec]
      rw [Category.assoc]
      --letI : BraidedCategory C := CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory
      simp only [ Category.assoc]
      rw [plist.cons_rec]
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
      refine X ◁ plist.rec plist.nil (g ▷ plist X' (𝟙_ C) ≫ plist.cons) ≫= ?_
      simp only [comp_whiskerRight, assoc]
      have :  g ▷ plist X' (𝟙_ C) ≫ X' ◁ plist.rec η (h ▷ f.X ≫
        (μ :  f.X ⊗ f.X ⟶ f.X)) ≫ h ▷ f.X ≫ (μ : f.X ⊗ f.X ⟶ f.X)=
       (g ▷ plist X' (𝟙_ C) ≫ X' ◁ plist.rec η (h ▷ f.X ≫ (μ : f.X ⊗ f.X ⟶ f.X)))
         ≫ (h ▷ f.X ≫ (μ : f.X ⊗ f.X ⟶ f.X)) := by {simp only [Mon_.forget_obj, assoc]}
      rw [this]; clear this
      have :  X ◁ plist.rec η (h ▷ f.X ≫ (μ : f.X ⊗ f.X ⟶ f.X)) ≫
         g ▷ f.X ≫ h ▷ f.X ≫ (μ : f.X ⊗ f.X ⟶ f.X) =
       (X ◁ plist.rec η (h ▷ f.X ≫ (μ : f.X ⊗ f.X ⟶ f.X)) ≫
        g ▷ f.X) ≫ (h ▷ f.X ≫ (μ : f.X ⊗ f.X ⟶ f.X)) := by {
          simp only [Mon_.forget_obj, assoc]}
      rw [this]; clear this
      refine ?_ =≫ h ▷ f.X ≫ (μ : f.X ⊗ f.X ⟶ f.X)
      exact Eq.symm (whisker_exchange g (plist.rec η (h ▷ f.X ≫ (μ : f.X ⊗ f.X ⟶ f.X))))}
    homEquiv_naturality_right f g := by {
      dsimp [homEquiv]; rw [Category.assoc]
    }
  }

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
  dsimp [list.flatten, list.rec, list, list.nil]
  simp only [plist.nil_rec]

--flatten (xs:xss) = xs ++ flatten xss
theorem flatten_cons {A : C} :
  list.cons ≫ list.flatten = (list A ◁ list.flatten (A:=A)) ≫ list.append (A:=A) := by
  dsimp [list.flatten, list.rec, list.cons]
  rw [plist.cons_rec]

theorem join_cons {A : C} :
  list.cons ≫ list.join = list A ◁ list.join (A:=A) ≫ list.append := by {
    dsimp [cons,join]
    sorry
  }

theorem join_eq_flatten {A : C} : list.join (A := A) = list.flatten := by {
  dsimp [flatten,rec]
  apply plist.rec_uniq
  · rw [← join_nil, nil]
  · have := join_cons (A:=A)
    dsimp [cons] at this
    exact this
}

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
    simp only [id_whiskerRight, id_comp, Category.assoc]
    rw [list.cons, plist.cons_rec, list.nil]
    simp only [plist.whiskerLeft_nil_whiskerLeft_rec_assoc,
      Mon_Class.mul_one, Iso.inv_hom_id]
  assoc := by
    dsimp [monad, freeMonForgetAdjunction, map, plist.map, plist.rec]
    dsimp [homEquiv]
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
  rw [plist.cons_rec, list.nil]
  simp only [id_whiskerRight, id_comp, plist.whiskerLeft_nil_whiskerLeft_rec_assoc,
    Mon_Class.mul_one, Iso.inv_hom_id]

theorem aggregator_join {M : Mon_ C} :
  list.join ≫ aggregator M = (list.map <| aggregator M) ≫ aggregator M := by {
    dsimp [list.join, aggregator]
    have := (list.algebra.ofMon M).assoc
    dsimp [ofMon] at *
    rw [this]; clear this
    refine _ ≫= ?_
    simp only
  }

/-- Theorem: Aggregator is functorial. -/
theorem aggregator_map {M : Mon_ C} {f : M.X ⟶ M'.X} :
  list.map f ≫ aggregator M' = aggregator M ≫ f := by {
  have := (list.algebra.ofMon M).unit
  dsimp [aggregator,ofMon] at *
  dsimp [map,plist.map,plist.rec,lift,foldr]
  have := Adjunction.homEquiv_symm_id (Recursive.freeForgetAdj M'.X) (C:=C)
  sorry
  }

end list

end CategoryTheory
