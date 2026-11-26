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

/-- Any two list objects on the same object are isomorphic. -/
def IsList.iso {A L₁ L₂ : C} {nil₁ : 𝟙_ C ⟶ L₁} {cons₁ : A ⊗ L₁ ⟶ L₁}
    {nil₂ : 𝟙_ C ⟶ L₂} {cons₂ : A ⊗ L₂ ⟶ L₂}
    [IsList A L₁ nil₁ cons₁] [IsList A L₂ nil₂ cons₂] :
    L₁ ≅ L₂ :=
  { hom := IsList.rc nil₁ cons₁ nil₂ cons₂
    inv := IsList.rc nil₂ cons₂ nil₁ cons₁
    hom_inv_id := by
      have h₁ : IsList.rc nil₁ cons₁ nil₂ cons₂ ≫ IsList.rc nil₂ cons₂ nil₁ cons₁
          = IsList.rc nil₁ cons₁ nil₁ cons₁ :=
        IsList.rc_uniq _
          (by rw [← Category.assoc, IsList.nil_rc, IsList.nil_rc])
          (by rw [← Category.assoc, IsList.cons_rc, Category.assoc, IsList.cons_rc,
                whiskerLeft_comp_assoc])
      rw [h₁, (IsList.rc_uniq (𝟙 L₁) (by simp) (by simp)).symm]
    inv_hom_id := by
      have h₁ : IsList.rc nil₂ cons₂ nil₁ cons₁ ≫ IsList.rc nil₁ cons₁ nil₂ cons₂
          = IsList.rc nil₂ cons₂ nil₂ cons₂ :=
        IsList.rc_uniq _
          (by rw [← Category.assoc, IsList.nil_rc, IsList.nil_rc])
          (by rw [← Category.assoc, IsList.cons_rc, Category.assoc, IsList.cons_rc,
                whiskerLeft_comp_assoc])
      rw [h₁, (IsList.rc_uniq (𝟙 L₂) (by simp) (by simp)).symm] }

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
    rw [← assoc,rightUnitor_inv_naturality, assoc, nil_prc, ← unitors_inv_equal,Iso.inv_hom_id_assoc]
  cons_rc {B f g} := by
    rw [← assoc, rightUnitor_inv_naturality, assoc]
    rw [whiskerLeft_comp]
    simp only [assoc]
    rw [whiskerLeft_rightUnitor_inv]
    refine (Iso.inv_comp_eq (ρ_ (A ⊗ L))).mpr ?_
    simp only [← assoc]
    rw [Iso.hom_inv_id, id_comp]
    simp only [assoc]
    refine (Iso.inv_comp_eq (α_ A L (𝟙_ C))).mp ?_
    rw [cons_prc]
  rc_uniq {B f g} r h_nil h_cons := by
    refine (Iso.eq_inv_comp (ρ_ L)).mpr ?_
    apply prc_uniq
    · simp only [whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
      rw [unitors_equal]
      rw [h_nil]
    · rw [← rightUnitor_naturality]
      nth_rw 2 [← assoc]
      rw [← comp_whiskerRight]
      rw [h_cons]
      simp only [whiskerRight_id, assoc, Iso.inv_hom_id, comp_id, whiskerLeft_comp,
        whiskerLeft_rightUnitor]

@[simps]
def List.ofPList (A : C) [PList A] : List A where
  L := PList.L A
  nil := PList.nil A
  cons := PList.cons A
  isList := IsList.ofIsPList

attribute [local instance] List.ofPList
attribute [instance] IsList.ofIsPList

/-- Any parameterized list object is isomorphic to any list object. -/
def List.isoPList (A : C) [PList A] [List A] :
    List.L A ≅ PList.L A :=
  @IsList.iso _ _ _ A (List.L A) (PList.L A) _ _ (PList.nil A) (PList.cons A)
    (List.isList) (IsList.ofIsPList)

end

namespace List

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

open IsList

variable {A : C} [List A]

abbrev rc {B : C} (f : 𝟙_ C ⟶ B) (g : A ⊗ B ⟶ B) : List.L A ⟶ B :=
  IsList.rc (nil A) (cons A) f g

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
  dsimp [map]
  rw [cons_rc]
  simp only [← assoc]
  refine ?_ =≫ _
  rw [tensorHom_def']

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
  · rw [← assoc]
    rw [cons_rc]
    simp only [assoc, cons_rc, whiskerLeft_comp, comp_whiskerRight]
    simp only [← assoc]
    refine ?_ =≫ cons A''
    refine ?_ =≫ _
    dsimp [rc]
    simp only [assoc]
    refine _ ≫= ?_
    exact
      Eq.symm (whisker_exchange f
      (IsList.rc (nil A') (cons A') (nil A'') (g ▷ L A'' ≫ cons A'')))

section

variable (A)

/-- The singleton list morphism. In types, `singleton a = [a]`. -/
def singleton : A ⟶ L A :=
  (ρ_ _).inv ≫ (A ◁ nil A) ≫ cons A

/-- splits a list into its head and tail?, if the list is non-empty, else returns the empty list. -/
noncomputable def splitHeadTail [HasBinaryCoproducts C] : L A ⟶ 𝟙_ C ⨿ A ⊗ L A :=
  rc (coprod.inl) ((A ◁ coprod.desc (nil A) (cons A)) ≫ coprod.inr)

section splitHeadTail

variable {A}

-- splitHeadTail [] = inl ()
@[reassoc (attr := simp)]
theorem nil_splitHeadTail [HasBinaryCoproducts C] :
    nil A ≫ splitHeadTail A = coprod.inl := by
  dsimp [splitHeadTail]
  rw [nil_rc]

-- `fun as => if splitHeadTail (as) = inl (nil) return nil else cons splitHeadTail as = fun as => as`
@[reassoc (attr := simp)]
theorem splitHeadTail_nil_cons [HasBinaryCoproducts C] :
    splitHeadTail A ≫ coprod.desc (nil A) (cons A) = 𝟙 (L A) := by
  have h : splitHeadTail A ≫ coprod.desc (nil A) (cons A)
      = IsList.rc (nil A) (cons A) (nil A) (cons A) :=
    IsList.rc_uniq _
      (by dsimp [splitHeadTail]; rw [← Category.assoc, IsList.nil_rc, coprod.inl_desc])
      (by dsimp [splitHeadTail]
          rw [← Category.assoc, IsList.cons_rc, Category.assoc, Category.assoc, coprod.inr_desc,
              ← Category.assoc, ← whiskerLeft_comp])
  rw [h, (IsList.rc_uniq (𝟙 (L A)) (by simp) (by simp)).symm]

-- `fun (a, as) => splitHeadTail (a :: as) = fun (a, as) => inr (a, as)`
@[reassoc (attr := simp)]
theorem cons_splitHeadTail [HasBinaryCoproducts C] :
    cons A ≫ splitHeadTail A = coprod.inr := by
  have : cons A ≫ splitHeadTail A
      = A ◁ (splitHeadTail A ≫ coprod.desc (nil A) (cons A)) ≫ coprod.inr := by
    dsimp [splitHeadTail]; rw [IsList.cons_rc, ← Category.assoc, ← whiskerLeft_comp]
  rw [this, splitHeadTail_nil_cons, whiskerLeft_id, Category.id_comp]

end splitHeadTail

@[simps]
noncomputable def splitHeadTailIso [HasBinaryCoproducts C] : L A ≅ 𝟙_ C ⨿ A ⊗ L A where
  hom := splitHeadTail A
  inv := coprod.desc (nil A) (cons A)
  hom_inv_id := splitHeadTail_nil_cons
  inv_hom_id := by
    refine coprod.hom_ext ?_ ?_
    · simp only [coprod.desc_comp, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.ι_app_left,
      BinaryCofan.mk_inl, comp_id]
      exact nil_splitHeadTail
    · simp only [coprod.desc_comp, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.ι_app_right,
      BinaryCofan.mk_inr, comp_id]
      exact cons_splitHeadTail

end

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
    rw [← leftUnitor_naturality]
    simp only [← assoc]
    simp only [id_whiskerLeft, assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, comp_id]
    refine (Iso.inv_comp_eq (λ_ (List.L (𝟙_ C)))).mp ?_
    rw [← assoc, h_cons]

@[simps]
def NNO.ofListUnit [List (𝟙_ C)] : NNO C where
  N := List.L (𝟙_ C)
  zero := List.nil (𝟙_ C)
  succ := (λ_ _).inv ≫ List.cons (𝟙_ C)
  isNNO := IsNNO.ofListUnitNilCons

def NNO.ofListUnitIso [List (𝟙_ C)] [NNO C] :
    NNO.ofListUnit.N ≅ NNO.N (C:= C) :=
  @IsNNO.iso _ _ _ NNO.ofListUnit.N NNO.N _ _ _ _ NNO.ofListUnit.isNNO NNO.isNNO

/-- An isomorphism between the list object on the unit and the natural number object. -/
def isoListUnitNNO [List (𝟙_ C)] [NNO C] :
    List.L (𝟙_ C) ≅ NNO.N :=
  NNO.ofListUnitIso

end

namespace List

open NNO SemiCartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [SemiCartesianMonoidalCategory C]

variable (A : C) [List A]

noncomputable abbrev tail? [HasBinaryCoproducts C] : L A ⟶ 𝟙_ C ⨿ L A :=
  splitHeadTail A ≫ (coprod.map (𝟙 _) (SemiCartesianMonoidalCategory.snd A (L A)))

section tail?

variable [HasBinaryCoproducts C]

@[reassoc (attr := simp)]
theorem nil_tail? : nil A ≫ tail? A = coprod.inl := by
  dsimp [tail?, splitHeadTail]
  rw [← assoc]
  dsimp [rc]
  simp only [IsList.nil_rc, coprod.inl_map, id_comp]

@[simp]
theorem cons_tail? : cons A ≫ tail? A = snd A (L A) ≫ coprod.inr := by
  simp only [cons_splitHeadTail_assoc, coprod.inr_map]

@[simp]
theorem singleton_tail? :
    singleton A ≫ tail? A = toUnit A ≫ nil A ≫ coprod.inr := by
  dsimp [tail?, singleton]
  simp only [assoc, cons_splitHeadTail_assoc, coprod.inr_map, snd_def,
    whisker_exchange_assoc, leftUnitor_naturality_assoc]
  have h : (ρ_ A).inv ≫ (isTerminalTensorUnit.from A ▷ (𝟙_ C)) ≫ (λ_ (𝟙_ C)).hom = toUnit A :=
    toUnit_unique _ _
  rw [reassoc_of% h]

/-- `tail?` for the unit list object is isomorphic to `pred?` on the natural
number object. -/
theorem tail?_pred? [List (𝟙_ C)] [NNO C] :
      tail? (𝟙_ C) ≫ (coprod.map (𝟙 _) isoListUnitNNO.hom) =
        isoListUnitNNO.hom ≫ NNO.pred? (C:= C) := by
  have hnil_iso : nil (𝟙_ C) ≫ isoListUnitNNO.hom = NNO.zero :=
    @IsNNO.zero_rc _ _ _ _ _ _ NNO.ofListUnit.isNNO _ _ _
  have hcons_iso : ((λ_ (L (𝟙_ C))).inv ≫ cons (𝟙_ C)) ≫ isoListUnitNNO.hom
      = isoListUnitNNO.hom ≫ NNO.succ :=
    @IsNNO.succ_rc _ _ _ _ _ _ NNO.ofListUnit.isNNO _ _ _
  have hcons_succ : cons (𝟙_ C) ≫ isoListUnitNNO.hom
      = (λ_ (L (𝟙_ C))).hom ≫ isoListUnitNNO.hom ≫ NNO.succ := by
    rw [← hcons_iso]; simp [← Category.assoc]
  have hsnd : snd (𝟙_ C) (L (𝟙_ C)) = (λ_ (L (𝟙_ C))).hom := by
    rw [snd_def, show (isTerminalTensorUnit.from (𝟙_ C) : 𝟙_ C ⟶ 𝟙_ C) = 𝟙 (𝟙_ C)
      from toUnit_unique _ _, id_whiskerRight, Category.id_comp]
  rw [← cancel_epi (splitHeadTailIso (A := 𝟙_ C)).inv]
  show coprod.desc (nil (𝟙_ C)) (cons (𝟙_ C)) ≫ tail? (𝟙_ C)
        ≫ coprod.map (𝟙 _) isoListUnitNNO.hom
      = coprod.desc (nil (𝟙_ C)) (cons (𝟙_ C)) ≫ isoListUnitNNO.hom ≫ NNO.pred?
  apply coprod.hom_ext
  · rw [coprod.inl_desc_assoc, coprod.inl_desc_assoc, ← Category.assoc, nil_tail?,
        coprod.inl_map, Category.id_comp, ← Category.assoc, hnil_iso, NNO.pred?_zero]
  · rw [coprod.inr_desc_assoc, coprod.inr_desc_assoc, ← Category.assoc, cons_tail?,
        Category.assoc, coprod.inr_map, hsnd, ← Category.assoc (cons (𝟙_ C)), hcons_succ,
        Category.assoc, Category.assoc, NNO.pred?_succ]

end tail?

attribute [local instance] NNO.ofListUnit

abbrev len [NNO C]: L A ⟶ NNO.N :=
  rc NNO.zero (snd A NNO.N ≫ NNO.succ)

/-- The length of a list. -/
abbrev len' [List (𝟙_ C)] : L A ⟶ ofListUnit.N :=
  List.map <| SemiCartesianMonoidalCategory.toUnit A

section len

open SemiCartesianMonoidalCategory PList

variable [NNO C]

attribute [local instance] ofListUnit

variable {A}

theorem len_eq_len' [List (𝟙_ C)] :
    len A = len' A ≫ isoListUnitNNO.hom := by
  symm
  apply IsList.rc_uniq
  · rw [← assoc]
    show (nil A ≫ map (toUnit A)) ≫ isoListUnitNNO.hom = NNO.zero
    rw [nil_map]
    exact IsList.nil_rc
  · rw [← assoc]
    show (cons A ≫ map (toUnit A)) ≫ isoListUnitNNO.hom
        = (A ◁ (len' A ≫ isoListUnitNNO.hom)) ≫ snd A NNO.N ≫ NNO.succ
    rw [cons_map, assoc]
    have hcons : cons (𝟙_ C : C) ≫ isoListUnitNNO.hom
        = ((𝟙_ C) ◁ isoListUnitNNO.hom) ≫ ((λ_ NNO.N).hom ≫ NNO.succ) := IsList.cons_rc
    rw [hcons, snd_def]
    show (toUnit A ⊗ₘ map (toUnit A)) ≫ ((𝟙_ C) ◁ isoListUnitNNO.hom) ≫
          (λ_ NNO.N).hom ≫ NNO.succ
        = (A ◁ (len' A ≫ isoListUnitNNO.hom)) ≫
          (isTerminalTensorUnit.from A ▷ NNO.N ≫ (λ_ NNO.N).hom) ≫ NNO.succ
    rw [tensorHom_def, assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
        ← whisker_exchange_assoc]
    simp only [assoc, len']
    rfl

theorem len_def :
    len A = List.rc NNO.zero (snd A NNO.N ≫ NNO.succ) := by
  rfl

@[reassoc (attr := simp)]
theorem nil_len_zero : nil (A := A) ≫ len A = NNO.zero := by
  simp

theorem cons_len_succ :
    cons A ≫ len A = (A ◁ len A) ≫ snd A NNO.N ≫ NNO.succ := by
  aesop

-- len (a :: xs) = succ (len xs)
theorem cons_len_succ' [List (𝟙_ C)] :
    cons A ≫ len A = (toUnit A ⊗ₘ len A) ≫ (λ_ NNO.N).hom ≫ NNO.succ := by
  rw [cons_len_succ, snd_def, tensorHom_def]
  simp only [assoc, whisker_exchange_assoc, leftUnitor_naturality_assoc]
  rfl

theorem cons_len_eq_toUnit_map_cons_iso [List (𝟙_ C)] :
    cons A ≫ len A = (toUnit A ⊗ₘ map (toUnit A)) ≫ cons (𝟙_ C) ≫ isoListUnitNNO.hom := by
  rw [len_eq_len', ← assoc, cons_map, assoc]

-- len ([x]) = 1
theorem singleton_len_one :
    singleton A ≫ len A = toUnit A ≫ NNO.one := by
  dsimp [singleton]
  rw [assoc, assoc, cons_len_succ, ← whiskerLeft_comp_assoc, nil_len_zero, snd_def]
  simp only [assoc, whisker_exchange_assoc, leftUnitor_naturality_assoc]
  have h : (ρ_ A).inv ≫ (isTerminalTensorUnit.from A ▷ (𝟙_ C)) ≫ (λ_ (𝟙_ C)).hom = toUnit A :=
    toUnit_unique _ _
  rw [reassoc_of% h]
  simp [NNO.one]

end len

end List

abbrev WithList (C : Type u) [Category.{v} C] [MonoidalCategory C] := Π (A : C), List A

def WithList.ofWithPList (C : Type u) [Category.{v} C] [MonoidalCategory C] [WithPList C] :
    WithList C :=
  fun A => List.ofPList A

/-- The object of nonempty lists. -/
class NeList {C : Type u} [Category.{v} C] [SemiCartesianMonoidalCategory C] [HasBinaryCoproducts C]
    (A : C) [List A] where
  /-- The underlying nonempty list object on `A`. -/
  iL : C
  /-- The inclusion morphism from nonempty lists to lists. -/
  toList (A) : iL ⟶ List.L A
  /-- The tail? list -/
  tail (A) : iL ⟶ List.L A
  /-- The universal property of the nonempty list object. -/
  isPullback : IsPullback (tail) (toList) coprod.inr (List.tail? A)

namespace NeList

open IsPullback SemiCartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [SemiCartesianMonoidalCategory C] [HasBinaryCoproducts C]
variable {A : C} [List A] [NeList A]

theorem isMono_nelistToList : Mono (toList A) := by
  sorry

variable (A)

/-- The singelton list is a nonempty list. -/
noncomputable def singleton : A ⟶ NeList.iL A :=
  lift isPullback (toUnit A ≫ List.nil A) (List.singleton A)
    (by simp only [assoc, List.singleton_tail?])

attribute [local instance] NNO.ofListUnit

/-- The length of a nonempty list is the length of the underlying list. -/
def len [NNO C] : NeList.iL A ⟶ NNO.N :=
  toList A ≫ List.len A

section len

variable [NNO C]

theorem len_eq_tail_len_succ :
    len A = tail A ≫ List.len A ≫ NNO.succ := by
  have hkey : List.tail? A ≫ coprod.desc NNO.zero (List.len A ≫ NNO.succ) = List.len A := by
    rw [← cancel_epi (@List.splitHeadTailIso _ _ _ A _ _).inv,
        show (@List.splitHeadTailIso _ _ _ A _ _).inv
              = coprod.desc (List.nil A) (List.cons A) from rfl]
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc_assoc, coprod.inl_desc_assoc, ← Category.assoc,
          List.nil_tail?, coprod.inl_desc, List.nil_len_zero]
    · rw [coprod.inr_desc_assoc, coprod.inr_desc_assoc, ← Category.assoc, List.cons_tail?,
          Category.assoc, coprod.inr_desc, List.cons_len_succ, ← Category.assoc,
          ← Category.assoc (A ◁ List.len A)]
      congr 1
      rw [snd_def, snd_def, Category.assoc]
      slice_rhs 1 2 => rw [whisker_exchange]
      rw [Category.assoc, leftUnitor_naturality]
  simp only [len]
  rw [← hkey, ← Category.assoc, ← NeList.isPullback.w, Category.assoc, coprod.inr_desc, hkey]

end len

end NeList

end MonoidalCategory

section ListAsEndofunctorAlgebra

open List Endofunctor Algebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasBinaryCoproducts C]

namespace Endofunctor.Algebra

/-- The algebra associated to the parameterized list object `plist A P` for the endofunctor `X ↦ 𝟙_ C ⨿ (A ⊗ X)`. -/
noncomputable def ofList (A : C) [List A] :
    Algebra (linearPolynomial A (𝟙_ C)) :=
  linearPolynomialAlgebraMk (L A) (nil A) (cons A)

theorem OfList_a {A : C} [List A] :
    (ofList A).a = L A := by
  rfl

theorem ofList_str {A : C} [List A] :
    (ofList A).str = coprod.desc (nil A) (cons A) := by
  rfl

/-- In a list-arithmetic category, the parametrize list object is the initial algebra for the
polynomial endofunctor `X ↦ P ⨿ A ⊗ X`. -/
noncomputable instance ofListIsInitial {A : C} [List A] :
    IsInitial (Endofunctor.Algebra.ofList A) := by
  refine IsInitial.ofUniqueHom (fun α => ?_) ?_
  · refine
      { f := rc (linearPolynomialAlgebra.nil α) (linearPolynomialAlgebra.cons α)
        h := ?_ }
    change coprod.map (𝟙 _) (A ◁ rc (linearPolynomialAlgebra.nil α)
          (linearPolynomialAlgebra.cons α)) ≫ α.str
        = coprod.desc (MonoidalCategory.List.nil A) (MonoidalCategory.List.cons A)
            ≫ rc (linearPolynomialAlgebra.nil α) (linearPolynomialAlgebra.cons α)
    rw [coprod.desc_comp]
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_map_assoc, id_comp, coprod.inl_desc, IsList.nil_rc,
        linearPolynomialAlgebra.nil]
    · rw [coprod.inr_map_assoc, coprod.inr_desc, IsList.cons_rc, linearPolynomialAlgebra.cons]
  · intro α m
    apply Algebra.Hom.ext
    have hm : coprod.map (𝟙 _) (A ◁ m.f) ≫ α.str = (ofList A).str ≫ m.f := m.h
    rw [ofList_str] at hm
    have hnil := congrArg (coprod.inl ≫ ·) hm
    have hcons := congrArg (coprod.inr ≫ ·) hm
    simp only [coprod.inl_map_assoc, coprod.inr_map_assoc, id_comp,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc] at hnil hcons
    exact @IsList.rc_uniq C _ _ A (List.L A) (MonoidalCategory.List.nil A)
      (MonoidalCategory.List.cons A) List.isList α.a
      (linearPolynomialAlgebra.nil α) (linearPolynomialAlgebra.cons α) m.f hnil.symm hcons.symm

/-- The Lambek isomorphism  `(𝟙_ C) ⨿ (A ⊗ L A) ≅ L A`. -/
noncomputable def isoOfList [WithList C] (A : C) : (𝟙_ C) ⨿ (A ⊗ L A) ≅ L A where
  hom := (ofList A).str
  inv := Algebra.Initial.strInv <| ofListIsInitial
  hom_inv_id := Algebra.Initial.right_inv _
  inv_hom_id := Algebra.Initial.left_inv _

attribute [local instance] WithList.ofWithPList

open PList

/-- Conversely, any initial algebra for the polynomial endofunctor `X ↦ P ⨿ A ⊗ X` gives rise to a
parameterized list object. -/
noncomputable def toList (A : C)
    (α : Algebra (linearPolynomial A (𝟙_ C))) (h : IsInitial α):
    List A where
  L := α.a
  nil := linearPolynomialAlgebra.nil α
  cons := linearPolynomialAlgebra.cons α
  isList :=
    { rc := fun {B} f g =>
        (h.to (linearPolynomialAlgebraMk B f g)).f
      nil_rc := fun {B f g} => by
        have hcomm := (h.to (linearPolynomialAlgebraMk B f g)).h
        dsimp [linearPolynomialAlgebra.nil, linearPolynomial,
          linearPolynomialAlgebraMk] at *
        rw [Category.assoc, ← hcomm, ← Category.assoc, coprod.inl_map, Category.id_comp,
          coprod.inl_desc]
      cons_rc := fun {B f g} => by
        have hcomm := (h.to (linearPolynomialAlgebraMk B f g)).h
        dsimp [linearPolynomialAlgebra.cons, linearPolynomial,
          linearPolynomialAlgebraMk] at *
        rw [Category.assoc, ← hcomm, ← Category.assoc, coprod.inr_map,
          Category.assoc, coprod.inr_desc]
      rc_uniq := fun {B f g} r h_nil h_cons => by
        let β : Algebra (linearPolynomial A (𝟙_ C)) := linearPolynomialAlgebraMk B f g
        have hr : coprod.map (𝟙 _) (A ◁ r) ≫ β.str = α.str ≫ r := by
          refine coprod.hom_ext ?_ ?_
          · rw [coprod.inl_map_assoc, Category.id_comp]
            change coprod.inl ≫ coprod.desc f g = coprod.inl ≫ α.str ≫ r
            rw [coprod.inl_desc, ← Category.assoc]; exact h_nil.symm
          · rw [coprod.inr_map_assoc]
            change A ◁ r ≫ coprod.inr ≫ coprod.desc f g = coprod.inr ≫ α.str ≫ r
            rw [coprod.inr_desc, ← Category.assoc]; exact h_cons.symm
        let φ : α ⟶ β := { f := r, h := hr }
        exact congrArg Algebra.Hom.f (h.hom_ext φ _) }

end Endofunctor.Algebra

end ListAsEndofunctorAlgebra

end CategoryTheory
