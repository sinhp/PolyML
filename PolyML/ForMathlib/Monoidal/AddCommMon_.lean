/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import PolyML.ForMathlib.Monoidal.AddMon_

/-!
# The category of additive commutative monoids in a braided monoidal category.
-/


universe v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory MonoidalCategory AddMon_Class

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

variable (C) in
/-- A commutative monoid object internal to a monoidal category.
-/
structure AddCommMon_ where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [mon : AddMon_Class X]
  [comm : IsAddCommMon X]

/-- Syntactic transfer of instances of `IsCommMon` to `IsAddCommMon`. -/
instance IsAddCommMon.fromIsCommMon {X : C} [MonObj X] [IsCommMonObj X] : IsAddCommMon X where
  add_comm := IsCommMonObj.mul_comm X

attribute [instance] AddCommMon_.mon AddCommMon_.comm

namespace AddCommMon_

/-- A commutative monoid object is a monoid object. -/
@[simps X]
def toAddMon_ (A : AddCommMon_ C) : AddMon_ C := ⟨A.X⟩

variable (C) in
/-- The trivial commutative monoid object. We later show this is initial in `AddCommMon_ C`.
-/
@[simps!]
def trivial : AddCommMon_ C := { X := 𝟙_ C }

instance : Inhabited (AddCommMon_ C) :=
  ⟨trivial C⟩

variable {M : AddCommMon_ C}

instance : Category (AddCommMon_ C) :=
  InducedCategory.category AddCommMon_.toAddMon_

@[simp]
theorem id_hom (A : AddCommMon_ C) : AddMon_.Hom.hom (𝟙 A) = 𝟙 A.X :=
  rfl

@[simp]
theorem comp_hom {R S T : AddCommMon_ C} (f : R ⟶ S) (g : S ⟶ T) :
    AddMon_.Hom.hom (f ≫ g) = f.hom ≫ g.hom :=
  rfl

@[ext]
lemma hom_ext {A B : AddCommMon_ C} (f g : A ⟶ B) (h : f.hom = g.hom) : f = g :=
  AddMon_.Hom.ext h

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/10688): the following two lemmas `id'` and `comp'`
-- have been added to ease automation;
@[simp]
lemma id' (A : AddCommMon_ C) : (𝟙 A : A.toAddMon_ ⟶ A.toAddMon_) = 𝟙 (A.toAddMon_) := rfl

@[simp]
lemma comp' {A₁ A₂ A₃ : AddCommMon_ C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    ((f ≫ g : A₁ ⟶ A₃) : A₁.toAddMon_ ⟶ A₃.toAddMon_) = @CategoryStruct.comp (AddMon_ C) _ _ _ _ f g := rfl

section

variable (C)

/-- The forgetful functor from commutative monoid objects to monoid objects. -/
def forget₂Mon_ : AddCommMon_ C ⥤ AddMon_ C :=
  inducedFunctor AddCommMon_.toAddMon_

/-- The forgetful functor from commutative monoid objects to monoid objects
is fully faithful. -/
def fullyFaithfulForget₂Mon_ : (forget₂Mon_ C).FullyFaithful :=
  fullyFaithfulInducedFunctor _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

instance : (forget₂Mon_ C).Full := InducedCategory.full _
instance : (forget₂Mon_ C).Faithful := InducedCategory.faithful _

@[simp]
theorem forget₂Mon_obj_one (A : AddCommMon_ C) : η[((forget₂Mon_ C).obj A).X] = η[A.X] :=
  rfl

@[simp]
theorem forget₂Mon_obj_mul (A : AddCommMon_ C) : μ[((forget₂Mon_ C).obj A).X] = μ[A.X] :=
  rfl

@[simp]
theorem forget₂Mon_map_hom {A B : AddCommMon_ C} (f : A ⟶ B) : ((forget₂Mon_ C).map f).hom = f.hom :=
  rfl

@[deprecated (since := "2025-02-07")] alias forget₂_Mon_obj_one := forget₂Mon_obj_one
@[deprecated (since := "2025-02-07")] alias forget₂_Mon_obj_mul := forget₂Mon_obj_mul
@[deprecated (since := "2025-02-07")] alias forget₂_Mon_map_hom := forget₂Mon_map_hom

/-- The forgetful functor from commutative monoid objects to the ambient category. -/
@[simps!]
def forget : AddCommMon_ C ⥤ C :=
  forget₂Mon_ C ⋙ AddMon_.forget C

instance : (forget C).Faithful where

@[simp]
theorem forget₂Mon_comp_forget : forget₂Mon_ C ⋙ AddMon_.forget C = forget C := rfl

end

section

variable {M N : AddCommMon_ C} (f : M.X ≅ N.X) (one_f : η[M.X] ≫ f.hom = η[N.X] := by aesop_cat)
  (mul_f : μ[M.X] ≫ f.hom = (f.hom ⊗ₘ f.hom) ≫ μ[N.X] := by aesop_cat)

/-- Constructor for isomorphisms in the category `AddCommMon_ C`. -/
def mkIso : M ≅ N :=
  (fullyFaithfulForget₂Mon_ C).preimageIso (AddMon_.mkIso f one_f mul_f)

@[simp] lemma mkIso_hom_hom : (mkIso f one_f mul_f).hom.hom = f.hom := rfl
@[simp] lemma mkIso_inv_hom : (mkIso f one_f mul_f).inv.hom = f.inv := rfl

end

instance uniqueHomFromTrivial (A : AddCommMon_ C) : Unique (trivial C ⟶ A) :=
  AddMon_.uniqueHomFromTrivial A.toAddMon_

open CategoryTheory.Limits

instance : HasInitial (AddCommMon_ C) :=
  hasInitial_of_unique (trivial C)

end AddCommMon_

namespace CategoryTheory
variable
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
  {F F' : C ⥤ D} [F.LaxBraided] [F'.LaxBraided] {G : D ⥤ E} [G.LaxBraided]

namespace Functor

open scoped Obj

instance isAddCommMon_obj {M : C} [AddMon_Class M] [IsAddCommMon M] : IsAddCommMon (F.obj M) where
  add_comm := by
    dsimp; rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsAddCommMon.add_comm]

variable (F) in
/-- A lax braided functor takes commutative monoid objects to commutative monoid objects.

That is, a lax braided functor `F : C ⥤ D` induces a functor `AddCommMon_ C ⥤ AddCommMon_ D`.
-/
@[simps!]
def mapAddCommMon : AddCommMon_ C ⥤ AddCommMon_ D where
  obj A :=
    { F.mapAddMon.obj A.toAddMon_ with
      comm :=
        { add_comm := by
            dsimp
            rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsAddCommMon.add_comm] } }
  map f := F.mapAddMon.map f

@[simp]
theorem mapAddCommMon_id_one (A : AddCommMon_ C) :
    η[((𝟭 C).mapAddCommMon.obj A).X] = 𝟙 _ ≫ η[A.X] :=
  rfl

@[simp]
theorem mapAddCommMon_id_mul (A : AddCommMon_ C) :
    μ[((𝟭 C).mapAddCommMon.obj A).X] = 𝟙 _ ≫ μ[A.X] :=
  rfl

@[simp]
theorem comp_mapAddCommMon_Cone (A : AddCommMon_ C) :
    η[((F ⋙ G).mapAddCommMon.obj A).X] = LaxMonoidal.ε (F ⋙ G) ≫ (F ⋙ G).map η[A.X] :=
  rfl

@[simp]
theorem comp_mapAddCommMon_mul (A : AddCommMon_ C) :
    μ[((F ⋙ G).mapAddCommMon.obj A).X] = LaxMonoidal.μ (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[A.X] :=
  rfl

/-- The identity functor is also the identity on commutative monoid objects. -/
@[simps!]
noncomputable def mapAddCommMonIdIso : mapAddCommMon (𝟭 C) ≅ 𝟭 (AddCommMon_ C) :=
  NatIso.ofComponents fun X ↦ AddCommMon_.mkIso (.refl _)

/-- The composition functor is also the composition on commutative monoid objects. -/
@[simps!]
noncomputable def mapAddCommMonCompIso : (F ⋙ G).mapAddCommMon ≅ F.mapAddCommMon ⋙ G.mapAddCommMon :=
  NatIso.ofComponents fun X ↦ AddCommMon_.mkIso (.refl _)

variable (C D) in
/-- `mapCommMon` is functorial in the lax braided functor. -/
@[simps]
def mapAddCommMonFunctor : LaxBraidedFunctor C D ⥤ AddCommMon_ C ⥤ AddCommMon_ D where
  obj F := F.mapAddCommMon
  map α := { app A := .mk' (α.hom.app A.X) }
  map_comp _ _ := rfl

/-- Natural transformations between functors lift to monoid objects. -/
@[simps!]
noncomputable def mapAddCommMonNatTrans (f : F ⟶ F') [NatTrans.IsMonoidal f] :
    F.mapAddCommMon ⟶ F'.mapAddCommMon where
  app X := .mk' (f.app _)

/-- Natural isomorphisms between functors lift to monoid objects. -/
@[simps!]
noncomputable def mapAddCommMonNatIso (e : F ≅ F') [NatTrans.IsMonoidal e.hom] :
    F.mapAddCommMon ≅ F'.mapAddCommMon :=
  NatIso.ofComponents fun X ↦ AddCommMon_.mkIso (e.app _)

end Functor

open Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Braided] [G.LaxBraided] [a.IsMonoidal]

/-- An adjunction of braided functors lifts to an adjunction of their lifts to commutative monoid
objects. -/
@[simps] noncomputable def mapAddCommMon : F.mapAddCommMon ⊣ G.mapAddCommMon where
  unit := mapAddCommMonIdIso.inv ≫ mapAddCommMonNatTrans a.unit ≫ mapAddCommMonCompIso.hom
  counit := mapAddCommMonCompIso.inv ≫ mapAddCommMonNatTrans a.counit ≫ mapAddCommMonIdIso.hom

end Adjunction

namespace Equivalence

/-- An equivalence of categories lifts to an equivalence of their commutative monoid objects. -/
@[simps]
noncomputable def mapAddCommMon (e : C ≌ D) [e.functor.Braided] [e.inverse.Braided] [e.IsMonoidal] :
    AddCommMon_ C ≌ AddCommMon_ D where
  functor := e.functor.mapAddCommMon
  inverse := e.inverse.mapAddCommMon
  unitIso := mapAddCommMonIdIso.symm ≪≫ mapAddCommMonNatIso e.unitIso ≪≫ mapAddCommMonCompIso
  counitIso := mapAddCommMonCompIso.symm ≪≫ mapAddCommMonNatIso e.counitIso ≪≫ mapAddCommMonIdIso

end CategoryTheory.Equivalence

namespace AddCommMon_

open CategoryTheory.LaxBraidedFunctor

namespace EquivLaxBraidedFunctorPUnit

variable (C) in
/-- Implementation of `AddCommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps]
def laxBraidedToAddCommMon : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ⥤ AddCommMon_ C where
  obj F := (F.mapAddCommMon : AddCommMon_ _ ⥤ AddCommMon_ C).obj (trivial (Discrete PUnit.{u+1}))
  map α := ((Functor.mapAddCommMonFunctor (Discrete PUnit) C).map α).app _

/-- Implementation of `AddCommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
def commMonToLaxBraidedObj (A : AddCommMon_ C) :
    Discrete PUnit.{u + 1} ⥤ C := (Functor.const _).obj A.X

instance (A : AddCommMon_ C) : (commMonToLaxBraidedObj A).LaxMonoidal where
  ε := η[A.X]
  «μ» _ _ := μ[A.X]

open Functor.LaxMonoidal

@[simp]
lemma commMonToLaxBraidedObj_ε (A : AddCommMon_ C) :
    ε (commMonToLaxBraidedObj A) = η[A.X] := rfl

@[simp]
lemma commMonToLaxBraidedObj_μ (A : AddCommMon_ C) (X Y) :
    «μ» (commMonToLaxBraidedObj A) X Y = μ[A.X] := rfl

instance (A : AddCommMon_ C) : (commMonToLaxBraidedObj A).LaxBraided where

variable (C)
/-- Implementation of `AddCommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps]
def addCommMonToLaxBraided : AddCommMon_ C ⥤ LaxBraidedFunctor (Discrete PUnit.{u + 1}) C where
  obj A := LaxBraidedFunctor.of (commMonToLaxBraidedObj A)
  map f :=
    { hom := { app := fun _ => f.hom }
      isMonoidal := { } }

/-- Implementation of `AddCommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
def unitIso :
    𝟭 (LaxBraidedFunctor (Discrete PUnit.{u + 1}) C) ≅
        laxBraidedToAddCommMon C ⋙ addCommMonToLaxBraided C :=
  NatIso.ofComponents
    (fun F ↦ LaxBraidedFunctor.isoOfComponents (fun _ ↦ F.mapIso (eqToIso (by ext))))
    (fun f ↦ by ext ⟨⟨⟩⟩; dsimp; simp)

@[simp]
theorem counitIso_aux_one (A : AddCommMon_ C) :
    η[((addCommMonToLaxBraided C ⋙ laxBraidedToAddCommMon C).obj A).X] = η[A.X] ≫ 𝟙 _ :=
  rfl

@[simp]
theorem counitIso_aux_mul (A : AddCommMon_ C) :
    μ[((addCommMonToLaxBraided C ⋙ laxBraidedToAddCommMon C).obj A).X] = μ[A.X] ≫ 𝟙 _ :=
  rfl

/-- Implementation of `AddCommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
def counitIso : addCommMonToLaxBraided C ⋙ laxBraidedToAddCommMon C ≅ 𝟭 (AddCommMon_ C) :=
  NatIso.ofComponents (fun F ↦ mkIso (Iso.refl _))

end EquivLaxBraidedFunctorPUnit

open EquivLaxBraidedFunctorPUnit

/-- Commutative monoid objects in `C` are "just" braided lax monoidal functors from the trivial
braided monoidal category to `C`.
-/
@[simps]
def equivLaxBraidedFunctorPUnit : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ≌ AddCommMon_ C where
  functor := laxBraidedToAddCommMon C
  inverse := addCommMonToLaxBraided C
  unitIso := unitIso C
  counitIso := counitIso C

end AddCommMon_
