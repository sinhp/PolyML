/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Monad.Monadicity
import PolyML.Monoidal.NNO

/-!
# Free Monoid Monad

In this file, we prove that in a list-arithmetic category, the list object `list A` is a free monoid on the object `A`.

This provides a left adjoint to the forgetful functor from `Mon_ C` to `C`.

The development here is a categorification of `Mathlib.Algebra.FreeMonoid.Basic` for types.
-/


namespace CategoryTheory

open Category CategoryTheory ListArithmetic MonoidalCategory Mon_Class NNO Limits

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [ListArithmetic C]


/-- The free monoid functor given by the list objects of a list-arithmetic category. -/
@[simps]
def freeMon : C ⥤ Mon_ C where
  obj A := Mon_.mk (list A)
  map {X Y} f := Mon_.Hom.mk' (list.map f) (list.map_nil) (list.append_map)
  map_id := by aesop
  map_comp := by aesop

/-- Extends the isomorphism `listUnitIsoNNO` of the types to the monoids. -/
def freeMonUnitIsoMonNNO [BraidedCategory C] :
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

variable {C}

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

variable (C)

variable (C)

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

section Monadicity

open Monad

instance hasReflexiveCoequalizersOfMon : HasReflexiveCoequalizers (Mon_ C) where
  has_coeq {A B} (f g) := sorry

instance preservesColimitOfIsReflexivePairOfMonForget :
    PreservesColimitOfIsReflexivePair (Mon_.forget C) where
  out {A B} (f g) r := sorry

instance monadicRightAdjointOfMonForget : MonadicRightAdjoint (Mon_.forget C) :=
  monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms <| freeMonForgetAdjunction C

end Monadicity

def monad : Monad C :=
  freeMonForgetAdjunction C |> Adjunction.toMonad

end list

def monToListAlgebraFunctor : Mon_ C ⥤ (list.monad C).Algebra :=
  Monad.comparison _

/-- The equivalence between the category of algebras for the `list` monad and the category of monoids in `C`. -/
instance monToListAlgebraFunctorIsEquivalence [ListArithmetic C] : (monToListAlgebraFunctor C).IsEquivalence := by
  refine MonadicRightAdjoint.eqv

namespace list

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

theorem join_cons {A : C} : list.cons ≫ list.join = list A ◁ list.join (A:=A) ≫ list.append := by
  sorry
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
@[simps!]
def ofMon (M : Mon_ C) : Monad.Algebra (monad C) := monToListAlgebraFunctor _ |>.obj M

@[simp]
theorem ofMon_a_eq {M : Mon_ C} : (ofMon M).a = list.lift (𝟙 M.X) := by
  dsimp [ofMon, monToListAlgebraFunctor, Monad.comparison]
  rfl

instance monClass (α : (monad C).Algebra) : Mon_Class α.A where
  one := nil ≫ α.a
  mul := (singleton ⊗ₘ singleton) ≫ append ≫ α.a
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry

noncomputable def monToListAlgebraFunctorIsEquivalence' : (monad C).Algebra ≌ Mon_ C :=
  (monToListAlgebraFunctor C).asEquivalence.symm

-- SH: an explicit and constructive/computable construction of the equivalence without recourse to the monadicity theorem
def equivalenceMon : (monad C).Algebra ≌ Mon_ C where
  functor := {
    obj α := ⟨α.A⟩
    map {α α'} f := Mon_.Hom.mk' f.1 (by sorry) (by sorry)
    map_id := sorry
    map_comp := sorry
  }
  inverse := monToListAlgebraFunctor C
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

end Algebra

open Algebra

def aggregator (M : Mon_ C) : list M.X ⟶ M.X :=
  (ofMon M).a

section aggregator

variable {M : Mon_ C}

theorem aggregator_one : η ≫ aggregator M = η := by
  exact lift_one

theorem aggregator_mul : μ ≫ aggregator M = (aggregator M ⊗ₘ aggregator M) ≫ μ := by
  exact lift_mul

theorem aggregator_singleton : list.singleton ≫ aggregator M = 𝟙 M.X := by
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
