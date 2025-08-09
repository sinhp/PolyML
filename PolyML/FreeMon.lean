/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Algebra
import PolyML.ListArithmetic

/-
In this file, we prove that in a list-arithmetic category, the list object `list A` is a free monoid on the object `A`.
Our development here is a categorification of `Mathlib.Algebra.FreeMonoid.Basic` for types.
-/

namespace CategoryTheory

open Category CategoryTheory Recursive ListArithmetic Functor MonoidalCategory Mon_Class Monad

universe v u

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] [ListArithmetic C]

/-- The free monoid functor given by the list objects of a list-arithmetic category. -/
@[simps]
def freeMon : C ⥤ Mon_ C where
  obj A := Mon_.mk (list A)
  map {X Y} f := Mon_.Hom.mk' (list.map f) (list.map_nil) (list.map_append)
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
  rw [plist.rec_nil]

theorem lift_mul {X : C} {M : Mon_ C} {f : X ⟶ M.X} :
    μ ≫ list.lift f = (list.lift f ⊗ₘ list.lift f) ≫ μ := by
  dsimp [Mon_Class.mul]
  dsimp [list.append]
  nth_rw 1 [lift,list.foldl]
  rw [tensorHom_def']
  letI : BraidedCategory C := CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory
  rw [← BraidedCategory.braiding_naturality_left_assoc]
  sorry
#check IsCommMon.mul_comm
def functor : C ⥤ C := freeMon C ⋙ Mon_.forget C

theorem functor_obj (A : C) : functor.obj A = list A := rfl

theorem functor_map {A B : C} (f : A ⟶ B) : functor.map f = list.map f := rfl

/-- The adjoint transposition equivalence of the hom-sets. -/
def homEquiv (X : C) (M : Mon_ C) : ((freeMon C).obj X ⟶ M) ≃ (X ⟶ (Mon_.forget C).obj M) where
  toFun := fun f => list.singleton ≫ f.hom
  invFun := fun f => (Mon_.Hom.mk' (list.lift f) list.lift_one list.lift_mul)
  left_inv := fun f => by {
    simp only [Mon_.forget_obj]
    dsimp [Mon_.Hom.mk']
    ext
    simp only [freeMon_obj_X]


    sorry
    --dsimp [lift,list.foldl]

    -- --nth_rw 2 [← plist.rec_nil (f:=f.hom)]
    -- apply plist.ext
    -- dsimp [list.lift,list.foldl]
    -- --simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc, plist.rec_nil]
    -- rw [← lift_one (f:=f.hom)]
    -- --simp only [freeMon_obj_X, MonoidalCategory.whiskerLeft_comp, Category.assoc, plist.rec_nil]
    -- --dsimp [list.lift,list.foldl]
    -- sorry
    -- sorry
  }

  right_inv := fun f => by {
    simp only [Mon_.forget_obj]
    dsimp [list.singleton]
    dsimp [lift,list.foldl]
    rw [← Category.assoc]
    rw [Category.assoc]
    dsimp [list.cons]
    rw [plist.rec_cons]
    rw [← Category.assoc]
    letI : BraidedCategory C := CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory
    simp only [Category.assoc]
    refine (Iso.inv_comp_eq (ρ_ X)).mpr ?_
    dsimp [list.nil]
    rw [← Category.assoc]
    simp only [plist.whisker_rec, BraidedCategory.braiding_naturality_right_assoc,
      braiding_tensorUnit_right, Category.assoc, Iso.cancel_iso_hom_left]
    refine (Iso.inv_comp_eq (λ_ X)).mpr ?_
    rw [← Category.assoc]
    sorry
    }

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
      simp only [plist.rec_nil]
    · dsimp [list.map, plist.map]
      rw [← Category.assoc]
      rw [plist.rec_cons]
      rw [Category.assoc]
      letI : BraidedCategory C := CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory
      simp only [ Category.assoc]
      rw [plist.rec_cons]
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
      refine X ◁ plist.rec plist.nil (g ▷ plist X' (𝟙_ C) ≫ plist.cons) ≫= ?_
      have :  g ▷ plist X' (𝟙_ C) ≫ X' ◁ plist.rec η ((β_ X' f.X).hom ≫ f.X ◁ h ≫ μ) ≫ (β_ X' f.X).hom ≫ f.X ◁ h ≫ μ =
        (g ▷ plist X' (𝟙_ C) ≫ X' ◁ plist.rec η ((β_ X' f.X).hom ≫ f.X ◁ h ≫ μ) ≫ (β_ X' f.X).hom) ≫ f.X ◁ h ≫ μ := by {
          simp only [Mon_.forget_obj,BraidedCategory.braiding_naturality_right_assoc,
            BraidedCategory.braiding_naturality_left_assoc,
            BraidedCategory.braiding_naturality_right, Category.assoc]}
      rw [this]
      have :  X ◁ plist.rec η ((β_ X' f.X).hom ≫ f.X ◁ h ≫ μ) ≫ (β_ X f.X).hom ≫ f.X ◁ g ≫ f.X ◁ h ≫ μ=
       (X ◁ plist.rec η ((β_ X' f.X).hom ≫ f.X ◁ h ≫ μ) ≫ (β_ X f.X).hom ≫ f.X ◁ g) ≫ f.X ◁ h ≫ μ := by {
        simp only [Mon_.forget_obj, BraidedCategory.braiding_naturality_right_assoc, Category.assoc]}
      rw [this]
      refine ?_ =≫ f.X ◁ h ≫ μ
      rename_i this_1 this_2
      simp_all only [Mon_.forget_obj, BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_naturality_left_assoc, BraidedCategory.braiding_naturality_right, Category.assoc,
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

theorem join_eq_flatten {A : C} : list.join (A := A) = list.flatten := by {
  dsimp [list.join]
  dsimp [list.flatten]
  dsimp [list.rec']
  apply plist.ext
  · dsimp [list.nil]
    dsimp [monad]
    dsimp [freeMonoidAdjunction, homEquiv]
    dsimp [lift]
    dsimp [list.foldl]
    simp only [MonoidalCategory.whiskerLeft_id, id_comp, plist.rec_nil]
    rfl
  · dsimp [monad, freeMonoidAdjunction, homEquiv]
    dsimp [lift, list.foldl]
    --simp only [MonoidalCategory.whiskerLeft_id, id_comp]
    rw [plist.rec_cons]
    letI : BraidedCategory C:= CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory
    nth_rw 2 [← BraidedCategory.braiding_naturality_left_assoc]
    rw [plist.rec_cons]
    nth_rw 2 [list.append]
    sorry
    --simp?
}

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
    rw [plist.rec_cons]
    letI : BraidedCategory C := CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory
    have : M.X ◁ list.nil ≫ M.X ◁ plist.rec η ((β_ M.X M.X).hom ≫ μ) =
    M.X ◁ (list.nil ≫ plist.rec η ((β_ M.X M.X).hom ≫ μ))  := by {
      simp only [MonoidalCategory.whiskerLeft_comp]}
    have h1 : (ρ_ M.X).inv ≫ M.X ◁ list.nil ≫ M.X ◁ plist.rec η
     ((β_ M.X M.X).hom ≫ μ) ≫ (β_ M.X M.X).hom ≫ μ =
     (ρ_ M.X).inv ≫ (M.X ◁ list.nil ≫ M.X ◁ plist.rec η
     ((β_ M.X M.X).hom ≫ μ)) ≫ (β_ M.X M.X).hom ≫ μ  := by {
      simp only [BraidedCategory.braiding_naturality_right_assoc,
        braiding_tensorUnit_right, Category.assoc, Iso.inv_hom_id_assoc]}
    rw [h1]
    rw [this]
    dsimp [list.nil]
    rw [plist.rec_nil]
    simp only [BraidedCategory.braiding_naturality_right_assoc, braiding_tensorUnit_right,
      Mon_Class.one_mul, Category.assoc, Iso.inv_hom_id, comp_id]
    }
  assoc := by {
    dsimp [monad, freeMonoidAdjunction, homEquiv,lift, list.foldl]
    simp only [MonoidalCategory.whiskerLeft_id, id_comp]
    letI :  BraidedCategory C := CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory
    refine ?_ =≫ plist.rec η ((β_ M.X M.X).hom ≫ μ)
    dsimp [list.map]
    dsimp [list]
    dsimp [plist.map]
    congr 1
    sorry

      -- rw [plist.rec_cons]
      -- simp only [plist.rec_nil, BraidedCategory.braiding_naturality_right_assoc]
      -- aesop_cat

    -- apply plist.ext
    -- · dsimp [monad, freeMonoidAdjunction, homEquiv]
    --   have := list.lift_one (C:=C) (f:= (𝟙 M.X))
    --   have := list.map_nil (C:=C) (f:= (lift (𝟙 M.X)))
    --   dsimp [list,list.nil] at this
    --   rw [← Category.assoc]
    --   rw [← Category.assoc]
    --   rw [this]
    --   simp only [Category.assoc]
    --   rw [← Category.assoc]
    --   refine ?_ =≫ lift (𝟙 M.X)
    --   dsimp [lift,list.foldl]
    --   simp only [MonoidalCategory.whiskerLeft_id, id_comp, plist.rec_nil]
    --   rfl
    -- · dsimp [monad, freeMonoidAdjunction, homEquiv]
    --   rw [← Category.assoc]
    --   rw [← Category.assoc]
    --   dsimp [list.map]
    --   rw [plist.map_cons]
    --   refine ?_ =≫ lift (𝟙 M.X)
    --   nth_rw 1 [lift,list.foldl]
    --   simp only [freeMon_obj_X, freeMon_obj_mon, MonoidalCategory.whiskerLeft_id, id_comp]
    --   rw [plist.rec_cons]
    --   simp only [BraidedCategory.braiding_naturality_right_assoc]
    --   dsimp [Mon_Class.mul]
    --   nth_rw 2 [list.append]

      -- have := list.map_cons (C:=C) (f:= (lift (𝟙 M.X)))
      -- dsimp [list.cons] at this
      -- rw [this]
      -- refine ?_ =≫ lift (𝟙 M.X)
      -- nth_rw 1 [lift,list.foldl]
      -- rw [plist.rec_cons]

      -- simp only [freeMon_obj_X, freeMon_obj_mon, MonoidalCategory.whiskerLeft_id, id_comp,
      --   plist.rec_nil, BraidedCategory.braiding_naturality_right_assoc]
      -- dsimp [Mon_Class.mul]
      -- dsimp [list.append]
      -- dsimp [list.rec]
      -- nth_rw 2 [lift]
      -- nth_rw 1 [list.foldl]
      -- simp only [freeMon_obj_X, freeMon_obj_mon, MonoidalCategory.whiskerLeft_id, id_comp]
      -- rw [plist.rec_cons]
      -- dsimp [list.map, plist.map]

  }

end algebra

open algebra

def aggregator (M : Mon_ C) : list M.X ⟶ M.X :=
  (ofMon M).a

theorem aggregator_one {M : Mon_ C} :
  η ≫ aggregator M = η :=
    lift_one

theorem aggregator_mul {M : Mon_ C} :
  μ ≫ aggregator M = (aggregator M ⊗ₘ aggregator M) ≫ μ := lift_mul

theorem aggregator_singleton {M : Mon_ C} :
    list.singleton ≫ aggregator M = 𝟙 M.X := by
  dsimp [aggregator, ofMon, list.singleton]
  simp only [Category.assoc]
  dsimp [lift, list.foldl, list.cons]
  rw [plist.rec_cons]
  dsimp [list.nil]
  letI : BraidedCategory C := CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory
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
  simp only [MonoidalCategory.whiskerLeft_id, id_comp, plist.rec_nil,
    BraidedCategory.braiding_naturality_right_assoc,
    braiding_tensorUnit_right, Mon_Class.one_mul,
    Category.assoc, Iso.inv_hom_id, comp_id]

theorem aggregator_join {M : Mon_ C} :
  list.join ≫ aggregator M = (list.map <| aggregator M) ≫ aggregator M := by
  rw [CategoryTheory.list.join_eq_flatten]
  dsimp [list.flatten]
  dsimp [list.rec']
  dsimp [aggregator, ofMon, list.singleton]
  rw [← plist.rec_uniq]
  · sorry
  · have := list.map_cons (C:=C) (f:= (lift (𝟙 M.X)))
    dsimp [list.cons] at this
    rw [this]
    --refine list M.X ◁ list.map (lift (𝟙 M.X)) ≫= ?_
    --dsimp [list.append]
    --dsimp [list.rec]
    dsimp [lift, list.foldl]
    letI : BraidedCategory C := CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory
    refine list M.X ◁ list.map (plist.rec η ((β_ M.X M.X).hom ≫ M.X ◁ 𝟙 M.X ≫ μ)) ≫= ?_
    simp only [MonoidalCategory.whiskerLeft_id, id_comp]
    dsimp [list.append,list.rec]
    refine (Iso.eq_inv_comp (plistIsoTensor M.X (list M.X))).mpr ?_
    refine
      plist.rec_uniq
        ((plistIsoTensor M.X (list M.X)).hom ≫
          plist.rec η ((β_ M.X M.X).hom ≫ μ) ▷ list M.X ≫ plist.cons)
        ?_ ?_
    dsimp [plistIsoTensor]
    rw [plist.map'_eq_rec]
    rw [← Category.assoc]
    rw [← Category.assoc]
    rw [← Category.assoc]
    rw [plist.rec_nil]
    simp only [Category.assoc]
    --refine (Iso.inv_comp_eq_id (λ_ (list M.X))).mpr ?_
    unfold plist.cmp
    simp only [plist.rec_nil_assoc]
    rw [← Category.assoc]
    letI : BraidedCategory C := CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory
    dsimp [list]
    simp only [plist.rec_nil, Category.assoc, comp_id, MonoidalCategory.whiskerLeft_id, id_comp,
      plist.rec_uniq]
    · sorry
    · dsimp [plistIsoTensor]
      simp only [Category.assoc]
      rw [plist.map'_eq_rec]
      rw [← Category.assoc]
      rw [plist.rec_cons]
      dsimp [list.cons]
      rw [← Category.assoc]
      simp only [Category.assoc,
        MonoidalCategory.whiskerLeft_comp]
      refine M.X ◁ plist.rec ((λ_ (list M.X)).inv ≫ plist.nil) plist.cons ≫= ?_
      unfold plist.cmp
      rw [← Category.assoc]
      rw [plist.rec_cons]
      simp only [Category.assoc]
      refine
        M.X ◁
            plist.rec (plist.nil ▷ list M.X)
              ((α_ M.X (plist M.X (𝟙_ C)) (list M.X)).inv ≫ plist.cons ▷ list M.X) ≫=
          ?_
      refine (Iso.inv_comp_eq (α_ M.X (plist M.X (𝟙_ C)) (list M.X))).mpr ?_
      rw [← Category.assoc]
      rw [← Category.assoc]
      rw [← Category.assoc]
      refine ?_ =≫ plist.cons
      simp only [Category.assoc]
      sorry

/-- Theorem: Aggregator is functorial. -/
theorem aggregator_map {M : Mon_ C} {f : M.X ⟶ M'.X} :
  list.map f ≫ aggregator M' = aggregator M ≫ f := by
  have := list.lift_one (C:=C) (f:= f)
  have := list.map_nil (C:=C) (f:= (lift (𝟙 M.X)))
  dsimp [aggregator, ofMon, list.singleton]
  dsimp [list.map]
  apply plist.ext
  simp only [plist.map_nil_assoc]
  · sorry
  · rw [← Category.assoc]
    rw [plist.map_cons]
    dsimp [lift,list.foldl]
    rw [Category.assoc]
    rw [Category.assoc]
    rw [plist.rec_cons]
    rw [← Category.assoc]
    rw [← Category.assoc]
    rw [← Category.assoc]
    rw [← Category.assoc]
    rw [← Category.assoc]
    rw [← Category.assoc]
    rw [plist.rec_cons]
    simp only [MonoidalCategory.whiskerLeft_id, comp_id, Category.assoc,
      BraidedCategory.braiding_naturality_right, BraidedCategory.braiding_naturality_left_assoc,
      BraidedCategory.braiding_naturality_right_assoc, id_comp, Iso.cancel_iso_hom_left]
    sorry

end list

end CategoryTheory
