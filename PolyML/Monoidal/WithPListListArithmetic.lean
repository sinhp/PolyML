/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import PolyML.Monoidal.ListArithmetic
import PolyML.Monoidal.PList

/-!
# List arithmetic from parameterized list objects

If every object carries a `PList` structure, we obtain `Recursive` and `ListArithmetic`.
-/

universe u v

namespace CategoryTheory

open MonoidalCategory PList IsPList ListArithmetic WithRecursion

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

instance (A : C) [PList A] : MonoidalCategory.WithRecursion A :=
  MonoidalCategory.WithRecursion.ofPList A

instance (A : C) [PList A] : CategoryTheory.WithRecursion A where
  freeActionFunctor := MonoidalCategory.WithRecursion.freeActionFunctor A
  freeForgetAdj := MonoidalCategory.WithRecursion.freeForgetAdj A

noncomputable instance [WithPList C] : Recursive C where
  withRec A := inferInstanceAs (CategoryTheory.WithRecursion A)

section

variable [WithPList C]

/-- In a `WithPList` category, the comparison morphism is the inverse associator. -/
theorem withPList_cmp_eq_associator (A P Y : C) :
    plist.cmp A P Y = (α_ (PList.L A) P Y).inv := by
  refine (plist.rc_uniq (r := (α_ (PList.L A) P Y).inv) ?_ ?_).symm
  · dsimp [plist.nil]
    change (MonoidalCategory.WithRecursion.freeForgetAdj A).unit.app (P ⊗ Y) ≫ (α_ (PList.L A) P Y).inv =
        (MonoidalCategory.WithRecursion.freeForgetAdj A).unit.app P ▷ Y
    rw [ofPList.freeForgetAdj_unit_app, ofPList.freeForgetAdj_unit_app, Category.assoc]
    aesop_cat
  · dsimp [plist.cons]
    change ((MonoidalCategory.WithRecursion.freeActionFunctor A).obj (P ⊗ Y)).str ≫ (α_ (PList.L A) P Y).inv =
        A ◁ (α_ (PList.L A) P Y).inv ≫ (α_ A (plist A P) Y).inv ≫
          ((MonoidalCategory.WithRecursion.freeActionFunctor A).obj P).str ▷ Y
    rw [withRecursionOfPList.freeActionFunctor_obj_str, withRecursionOfPList.freeActionFunctor_obj_str,
      Category.assoc]
    rw [show PList.cons A ▷ (P ⊗ Y) =
        (α_ (A ⊗ PList.L A) P Y).inv ≫ (PList.cons A ▷ P) ▷ Y ≫ (α_ (PList.L A) P Y).hom from
      whiskerRight_tensor (f := PList.cons A) (Y := P) (Z := Y)]
    have hc : (PList.cons A ▷ P) ▷ Y ≫ (α_ (PList.L A) P Y).hom ≫ (α_ (PList.L A) P Y).inv =
        (PList.cons A ▷ P) ▷ Y := by simp [Iso.hom_inv_id]
    rw [Category.assoc, Category.assoc, hc, ← Category.assoc]
    rw [Eq.symm (@pentagon_inv C _ _ A (PList.L A) P Y)]
    rw [Category.assoc, comp_whiskerRight, Category.assoc]
    rfl

noncomputable instance withPListListArithmetic : ListArithmetic C where
  cmpInv A P Y := (α_ (PList.L A) P Y).hom
  hom_inv_id := by
    intro A P Y
    rw [withPList_cmp_eq_associator]
    exact (α_ (PList.L A) P Y).inv_hom_id
  inv_hom_id := by
    intro A P Y
    rw [withPList_cmp_eq_associator]
    exact (α_ (PList.L A) P Y).hom_inv_id

end

end CategoryTheory
