/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import PolyML.Monoidal.PList
import PolyML.Monoidal.NNO


/-! # Non-parameterized list object in a monoidal category -/


universe u v

namespace CategoryTheory

open Category Opposite Limits MonoidalCategory

attribute [local instance] _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

namespace MonoidalCategory

open Endofunctor Algebra

section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

class IsList (A : C) (L : C) (nil : 𝟙_ C ⟶ L) (cons : A ⊗ L ⟶ L) where
  /-- The recursor morphism for the list object. -/
  rc {B : C} (f : 𝟙_ C ⟶ B) (g : A ⊗ B ⟶ B) : L ⟶ B
  /-- The nil case of the recursor. -/
  nil_rc {B : C} {f : 𝟙_ C ⟶ B} {g : A ⊗ B ⟶ B} :
    nil ≫ rc f g = f
  /-- The cons case of the recursor. -/
  cons_rc {B : C} {f : 𝟙_ C ⟶ B} {g : A ⊗ B ⟶ B} :
    cons ≫ rc f g = (A ◁ rc f g) ≫ g
  /-- The uniqueness of the recursor. -/
  rc_uniq {B : C} {f : 𝟙_ C ⟶ B} {g : A ⊗ B ⟶ B} (r : L ⟶ B)
    (h_nil : nil ≫ r = f)
    (h_cons: cons ≫ r = A ◁ r ≫ g) : r = rc f g

attribute [reassoc (attr := simp)] IsList.nil_rc IsList.cons_rc

class List (A : C) where
  /-- The underlying list object on `A`. -/
  L : C
  /-- The nil morphism for the list object `L A`. -/
  nil (A) : 𝟙_ C ⟶ L
  /-- The cons morphism for the list object `L A`. -/
  cons (A) : A ⊗ L ⟶ L
  /-- The universal property of the parameterized list object. -/
  [isList : IsList A L nil cons]

attribute [instance] List.isList

open IsPList

/-- Every Parameterized list object gives rise to a non-parameterized list object. -/
@[simps]
def IsList.ofIsPList {A : C} {L : C} {nil : 𝟙_ C ⟶ L} {cons : A ⊗ L ⟶ L}
    [IsPList A L nil cons] : IsList A L nil cons where
  rc {B} f g := (ρ_ _).inv ≫ IsPList.prc nil cons f g
  nil_rc {B f g} := by
    sorry
  cons_rc {B f g} := by
    sorry
  rc_uniq {B f g} r h_nil h_cons := by
    sorry

@[simps]
def List.ofPList (A : C) [PList A] : List A where
  L := PList.L A
  nil := PList.nil
  cons := PList.cons A
  isList := IsList.ofIsPList

end


namespace List

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

open IsList

variable {A : C} [List A]

abbrev rc {B : C} (f : 𝟙_ C ⟶ B) (g : A ⊗ B ⟶ B) : List.L A ⟶ B :=
  IsList.rc (nil A) (cons A) f g

/-- The singleton list morphism. In types, `singleton a = [a]`. -/
def singleton : A ⟶ L A :=
  (ρ_ _).inv ≫ (A ◁ nil A) ≫ cons A

/-- Covariant action of `List` on morphisms of the first argument.
A morphism `f : A ⟶ B` induces a morphism `List.map f ▷ P : List.L A ⊗ P ⟶ List.L B ⊗ P`. -/
def map {A' : C} [List A'] (f : A ⟶ A') : L A ⟶ L A' :=
  rc (nil A') (f ▷ (L A') ≫ cons A')

@[reassoc (attr := simp)]
theorem nil_map {A' : C} [List A'] (f : A ⟶ A') :
    nil A ≫ map f = nil A' := by
  simp only [map, rc, nil_rc]

@[reassoc (attr := simp)]
theorem cons_map {A' : C} [List A'] {f : A ⟶ A'} :
    cons A ≫ map f = (f ⊗ₘ map f) ≫ cons A' := by
  sorry

@[simp]
theorem map_id : map (𝟙 A) = 𝟙 (L A) := by
  dsimp [map]
  symm
  apply IsList.rc_uniq <;> simp

@[reassoc (attr := simp)]
theorem map_comp {A' A'' : C} [List A'] [List A''] (f : A ⟶ A') (g : A' ⟶ A'') :
  map (f ≫ g) = map f ≫ map g := by
  dsimp [map]
  symm
  apply IsList.rc_uniq
  · aesop
  · sorry

/-- Splits a list into its head and tail, if the list is non-empty, else returns the empty list. -/
noncomputable def split [HasBinaryCoproducts C] : L A ⟶ 𝟙_ C ⨿ A ⊗ L A :=
  rc (coprod.inl) ((𝟙 A ⊗ₘ coprod.desc (nil A) (cons A)) ≫ coprod.inr)

-- split [] = inl ()
@[reassoc (attr := simp)]
theorem nil_split [HasBinaryCoproducts C] :
    nil A ≫ split = coprod.inl := by
  dsimp [split]
  sorry

-- `fun (a, as) => split (a :: as) = fun (a, as) => inr (a, as)`
@[reassoc (attr := simp)]
theorem cons_split [HasBinaryCoproducts C] :
    cons A ≫ split = coprod.inr := by
  dsimp [split]
  sorry

-- `fun as => if split (as) = inl (nil) return nil else cons split as = fun as => as`
@[reassoc (attr := simp)]
theorem split_nil_cons [HasBinaryCoproducts C] :
    split ≫ coprod.desc (nil A) (cons A) = 𝟙 (L A) := by
  dsimp [split]
  sorry

variable (A) in
@[simps]
noncomputable def splitIso [HasBinaryCoproducts C] : L A ≅ 𝟙_ C ⨿ A ⊗ L A where
  hom := split
  inv := coprod.desc (nil A) (cons A)
  hom_inv_id := split_nil_cons
  inv_hom_id := by
    refine coprod.hom_ext ?_ ?_
    · simp only [coprod.desc_comp, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.ι_app_left,
      BinaryCofan.mk_inl, comp_id]
      exact nil_split
    · simp only [coprod.desc_comp, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.ι_app_right,
      BinaryCofan.mk_inr, comp_id]
      exact cons_split

end List

section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

@[simps]
def IsNNO.ofListUnitNilCons [List (𝟙_ C)] :
    IsNNO (List.L (𝟙_ C)) (List.nil (𝟙_ C)) ((λ_ _).inv ≫ List.cons (𝟙_ C)) where
  rc {B} f g := List.rc f ((λ_ B).hom ≫ g )
  zero_rc {B f g} := by simp
  succ_rc {B f g} := by simp
  rc_uniq {B f g r} h_nil h_cons := by
    apply IsList.rc_uniq r h_nil
    sorry

@[simps]
def NNO.ofListUnit [List (𝟙_ C)] : NNO C where
  N := List.L (𝟙_ C)
  zero := List.nil (𝟙_ C)
  succ := (λ_ _).inv ≫ List.cons (𝟙_ C)
  isNNO := IsNNO.ofListUnitNilCons

end

namespace List

open NNO SemiCartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [SemiCartesianMonoidalCategory C]

variable {A : C} [List A]

noncomputable abbrev tail [HasBinaryCoproducts C] : L A ⟶ 𝟙_ C ⨿ L A :=
  split ≫ (coprod.map (𝟙 _) (SemiCartesianMonoidalCategory.snd A (L A)))

@[reassoc (attr := simp)]
theorem nil_tail [HasBinaryCoproducts C] : nil A ≫ tail = coprod.inl := by
  dsimp [tail, split]
  rw [← assoc]
  dsimp [rc]
  sorry

@[simp]
theorem cons_tail [HasBinaryCoproducts C] : cons A ≫ tail = snd A (L A) ≫ coprod.inr := by
  sorry

@[simp]
theorem singleton_tail [HasBinaryCoproducts C] :
    singleton ≫ tail = toUnit A ≫ nil A ≫ coprod.inr := by
  sorry


attribute [local instance] NNO.ofListUnit

/-- The length of a list. -/
abbrev len [List (𝟙_ C)] : L A ⟶ ofListUnit.N :=
  List.map <| SemiCartesianMonoidalCategory.toUnit A

section length

open SemiCartesianMonoidalCategory

variable [List (𝟙_ C)]

attribute [local instance] ofListUnit

theorem len_eq_rc_zero_snd_succ :
    len (A := A) = List.rc NNO.zero (snd A NNO.N ≫ NNO.succ) := by
  sorry

@[reassoc (attr := simp)]
theorem nil_len_zero : nil (A := A) ≫ len = NNO.zero := by
  sorry

theorem cons_len_succ :
    cons A ≫ len = (A ◁ len) ≫ snd A NNO.N ≫ NNO.succ := by
  sorry

-- len (a :: xs) = succ (len xs)
theorem cons_len_succ' :
    cons A ≫ len = (toUnit A ⊗ₘ len) ≫ (λ_ NNO.N).hom ≫ NNO.succ := by
  sorry

theorem cons_len_eq_map_toUnit_cons :
    cons A ≫ len = A ◁ map (toUnit A) ≫ (toUnit A ▷ L (𝟙_ C)) ≫ cons (𝟙_ C) := by
  sorry

-- len ([x]) = 1
theorem singleton_len_one :
    singleton (A := A) ≫ len = toUnit A ≫ NNO.one := by
  sorry

end length

end List



end MonoidalCategory

end CategoryTheory
