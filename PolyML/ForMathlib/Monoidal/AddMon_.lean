/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.Algebra.Group.PUnit
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# The category of monoids in a monoidal category.

We define monoids in a monoidal category `C` and show that the category of monoids is equivalent to
the category of lax monoidal functors from the unit monoidal category to `C`.  We also show that if
`C` is braided, then the category of monoids is naturally monoidal.

-/

universe v₁ v₂ v₃ u₁ u₂ u₃ u

open Function CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
class AddMon_Class (X : C) where
  /-- The unit morphism of a monoid object. -/
  zero : 𝟙_ C ⟶ X
  /-- The addition morphism of a monoid object. -/
  add : X ⊗ X ⟶ X
  zero_add (X) : zero ▷ X ≫ add = (λ_ X).hom := by aesop_cat
  add_zero (X) : X ◁ zero ≫ add = (ρ_ X).hom := by aesop_cat
  -- Obviously there is some flexibility stating this axiom.
  -- This zero has left- and right-hand sides matching the statement of `Monoid.add_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  add_assoc (X) : (add ▷ X) ≫ add = (α_ X X X).hom ≫ (X ◁ add) ≫ add := by aesop_cat

namespace AddMon_Class

@[inherit_doc] scoped notation "μ" => AddMon_Class.add
@[inherit_doc] scoped notation "μ["M"]" => AddMon_Class.add (X := M)
@[inherit_doc] scoped notation "η" => AddMon_Class.zero
@[inherit_doc] scoped notation "η["M"]" => AddMon_Class.zero (X := M)

attribute [reassoc (attr := simp)] zero_add add_zero add_assoc

/-- Transfers an instance of `Mon_Class` to `AddMon_Class` so that we can define `toSemiring`. -/
instance fromMon_Class {X : C} [MonObj X] : AddMon_Class X where
  zero := MonObj.one
  add := MonObj.mul
  zero_add := MonObj.one_mul X
  add_zero := MonObj.mul_one X
  add_assoc := MonObj.mul_assoc X

@[simps]
instance : AddMon_Class (𝟙_ C) where
  zero := 𝟙 _
  add := (λ_ _).hom
  add_assoc := by monoidal_coherence
  add_zero := by monoidal_coherence

@[ext]
theorem ext {X : C} (h₁ h₂ : AddMon_Class X) (H : h₁.add = h₂.add) : h₁ = h₂ := by
  suffices h₁.zero = h₂.zero by cases h₁; cases h₂; subst H this; rfl
  trans (λ_ _).inv ≫ (h₁.zero ⊗ₘ h₂.zero) ≫ h₁.add
  · simp [tensorHom_def, H, ← unitors_equal]
  · simp [tensorHom_def']

end AddMon_Class

open scoped AddMon_Class

variable {M N O : C} [AddMon_Class M] [AddMon_Class N] [AddMon_Class O]

/-- The property that a morphism between monoid objects is a monoid morphism. -/
class IsAddMon_Hom (f : M ⟶ N) : Prop where
  zero_hom (f) : η ≫ f = η := by aesop_cat
  add_hom (f) : μ ≫ f = (f ⊗ₘ f) ≫ μ := by aesop_cat

attribute [reassoc (attr := simp)] IsAddMon_Hom.zero_hom IsAddMon_Hom.add_hom

instance : IsAddMon_Hom (𝟙 M) where

instance (f : M ⟶ N) (g : N ⟶ O) [IsAddMon_Hom f] [IsAddMon_Hom g] : IsAddMon_Hom (f ≫ g) where

instance {M N : C} [AddMon_Class M] [AddMon_Class N] (f : M ≅ N) [IsAddMon_Hom f.hom] :
   IsAddMon_Hom f.inv where
  zero_hom := by simp [Iso.comp_inv_eq]
  add_hom := by simp [Iso.comp_inv_eq]

variable (C) in
/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
structure AddMon_ where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [mon : AddMon_Class X]

attribute [instance] AddMon_.mon

namespace AddMon_

variable (C) in
/-- The trivial monoid object. We later show this is initial in `AddMon_ C`.
-/
@[simps!]
def trivial : AddMon_ C := mk (𝟙_ C)

instance : Inhabited (AddMon_ C) :=
  ⟨trivial C⟩

end AddMon_

namespace AddMon_Class

variable {M : C} [AddMon_Class M]

@[simp]
theorem zero_add_hom {Z : C} (f : Z ⟶ M) : (η[M] ⊗ₘ f) ≫ μ[M] = (λ_ Z).hom ≫ f := by
  rw [tensorHom_def'_assoc, zero_add, leftUnitor_naturality]

@[simp]
theorem add_zero_hom {Z : C} (f : Z ⟶ M) : (f ⊗ₘ η[M]) ≫ μ[M] = (ρ_ Z).hom ≫ f := by
  rw [tensorHom_def_assoc, add_zero, rightUnitor_naturality]

variable (M) in
@[reassoc]
theorem add_assoc_flip : M ◁ μ ≫ μ = (α_ M M M).inv ≫ μ ▷ M ≫ μ := by
  simp

end AddMon_Class

namespace AddMon_

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : AddMon_ C) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [is_mon_hom : IsAddMon_Hom hom]

attribute [instance] Hom.is_mon_hom

/-- Construct a morphism `M ⟶ N` of `AddMon_ C` from a map `f : M ⟶ N` and a `IsAddMon_Hom f` instance. -/
abbrev Hom.mk' {M N : AddMon_ C} (f : M.X ⟶ N.X)
    (zero_f : η ≫ f = η := by aesop_cat)
    (add_f : μ ≫ f = (f ⊗ₘ f) ≫ μ := by aesop_cat) : Hom M N :=
  have : IsAddMon_Hom f := ⟨zero_f, add_f⟩
  .mk f

/-- The identity morphism on a monoid object. -/
@[simps]
def id (M : AddMon_ C) : Hom M M := ⟨𝟙 M.X⟩

instance homInhabited (M : AddMon_ C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : AddMon_ C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

instance : Category (AddMon_ C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

instance {M N : AddMon_ C} (f : M ⟶ N) : IsAddMon_Hom f.hom := f.is_mon_hom

@[ext]
lemma Hom.ext' {M N : AddMon_ C} {f g : M ⟶ N} (w : f.hom = g.hom) : f = g :=
  Hom.ext w

lemma hom_injective {M N : AddMon_ C} : Injective (Hom.hom : (M ⟶ N) → (M.X ⟶ N.X)) :=
  fun _ _ ↦ Hom.ext

@[simp]
theorem id_hom' (M : AddMon_ C) : (𝟙 M : Hom M M).hom = 𝟙 M.X :=
  rfl

@[simp]
theorem comp_hom' {M N K : AddMon_ C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl

section

variable (C)

/-- The forgetful functor from monoid objects to the ambient category. -/
@[simps]
def forget : AddMon_ C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : (forget C).Faithful where

instance {A B : AddMon_ C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom :=
  e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e := ⟨⟨.mk' (inv f.hom), by aesop_cat⟩⟩

/-- Construct an isomorphism of monoids by giving an isomorphism between the underlying objects
and checking compatibility with unit and addition only in the forward direction.
-/
@[simps]
def mkIso' {M N : AddMon_ C} (f : M.X ≅ N.X) [IsAddMon_Hom f.hom] : M ≅ N where
  hom := Hom.mk f.hom
  inv := Hom.mk f.inv

/-- Construct an isomorphism of monoids by giving an isomorphism between the underlying objects
and checking compatibility with unit and addition only in the forward direction.
-/
@[simps!]
def mkIso {M N : AddMon_ C} (f : M.X ≅ N.X) (zero_f : η[M.X] ≫ f.hom = η[N.X] := by aesop_cat)
    (add_f : μ[M.X] ≫ f.hom = (f.hom ⊗ₘ f.hom) ≫ μ[N.X] := by aesop_cat) : M ≅ N :=
  have : IsAddMon_Hom f.hom := ⟨zero_f, add_f⟩
  mkIso' f

@[simps]
instance uniqueHomFromTrivial (A : AddMon_ C) : Unique (trivial C ⟶ A) where
  default :=
    { hom := η[A.X]
      is_mon_hom :=
        { add_hom := by simp [unitors_equal] } }
  uniq f := by
    ext
    rw [← Category.id_comp f.hom]
    dsimp only [trivial_X]
    rw [← trivial_mon_zero, IsAddMon_Hom.zero_hom]

open CategoryTheory.Limits

instance : HasInitial (AddMon_ C) :=
  hasInitial_of_unique (AddMon_.trivial C)

end AddMon_

namespace CategoryTheory
variable
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
  {F F' : C ⥤ D} {G : D ⥤ E}

namespace Functor

section LaxMonoidal
variable [F.LaxMonoidal] [F'.LaxMonoidal] [G.LaxMonoidal] (X Y : C) [AddMon_Class X] [AddMon_Class Y]
  (f : X ⟶ Y) [IsAddMon_Hom f]

/-- The image of a monoid object under a lax monoidal functor is a monoid object. -/
abbrev addMon_ClassObj : AddMon_Class (F.obj X) where
  zero := ε F ≫ F.map η
  add := LaxMonoidal.μ F X X ≫ F.map μ
  zero_add := by simp [← F.map_comp]
  add_zero := by simp [← F.map_comp]
  add_assoc := by
    simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, AddMon_Class.add_assoc]
    simp

scoped[Obj] attribute [instance] CategoryTheory.Functor.addMon_ClassObj

open scoped Obj

@[reassoc, simp] lemma obj.add_η_def : (η : 𝟙_ D ⟶ F.obj X) = ε F ≫ F.map η := rfl

@[reassoc, simp] lemma obj.add_μ_def : μ = LaxMonoidal.μ F X X ≫ F.map μ := rfl

instance map.instIsAddMon_Hom : IsAddMon_Hom (F.map f) where
  zero_hom := by simp [← map_comp]
  add_hom := by simp [← map_comp]

open AddMon_Class

-- TODO: mapMod F A : Mod A ⥤ Mod (F.mapAddMon A)
variable (F) in
/-- A lax monoidal functor takes monoid objects to monoid objects.

That is, a lax monoidal functor `F : C ⥤ D` induces a functor `AddMon_ C ⥤ AddMon_ D`.
-/
@[simps]
def mapAddMon : AddMon_ C ⥤ AddMon_ D where
  obj A := .mk (F.obj A.X)
  map f := .mk (F.map f.hom)

@[simp]
theorem id_mapAddMon_zero (X : AddMon_ C) : η[((𝟭 C).mapAddMon.obj X).X] = 𝟙 _ ≫ η[X.X] := rfl

@[simp]
theorem id_mapAddMon_add (X : AddMon_ C) : μ[((𝟭 C).mapAddMon.obj X).X] = 𝟙 _ ≫ μ[X.X] := rfl

@[simp]
theorem comp_mapAddMon_zero (X : AddMon_ C) :
    η[((F ⋙ G).mapAddMon.obj X).X] = ε (F ⋙ G) ≫ (F ⋙ G).map η[X.X] :=
  rfl

@[simp]
theorem comp_mapAddMon_add (X : AddMon_ C) :
    μ[((F ⋙ G).mapAddMon.obj X).X] = «μ» (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[X.X] :=
  rfl

/-- The identity functor is also the identity on monoid objects. -/
@[simps!]
noncomputable def mapAddMonIdIso : mapAddMon (𝟭 C) ≅ 𝟭 (AddMon_ C) :=
  NatIso.ofComponents fun X ↦ AddMon_.mkIso (.refl _)

/-- The composition functor is also the composition on monoid objects. -/
@[simps!]
noncomputable def mapAddMonCompIso : (F ⋙ G).mapAddMon ≅ F.mapAddMon ⋙ G.mapAddMon :=
  NatIso.ofComponents fun X ↦ AddMon_.mkIso (.refl _)

protected instance Faithful.mapAddMon [F.Faithful] : F.mapAddMon.Faithful where
  map_injective {_X _Y} _f _g hfg := AddMon_.Hom.ext <| map_injective congr(($hfg).hom)

/-- Natural transformations between functors lift to monoid objects. -/
@[simps!]
noncomputable def mapAddMonNatTrans (f : F ⟶ F') [NatTrans.IsMonoidal f] : F.mapAddMon ⟶ F'.mapAddMon where
  app X := .mk' (f.app _)

/-- Natural isomorphisms between functors lift to monoid objects. -/
@[simps!]
noncomputable def mapAddMonNatIso (e : F ≅ F') [NatTrans.IsMonoidal e.hom] : F.mapAddMon ≅ F'.mapAddMon :=
  NatIso.ofComponents fun X ↦ AddMon_.mkIso (e.app _)

end LaxMonoidal

section Monoidal
variable [F.Monoidal]

open scoped Obj

protected instance Full.mapAddMon [F.Full] [F.Faithful] : F.mapAddMon.Full where
  map_surjective {X Y} f :=
    let ⟨g, hg⟩ := F.map_surjective f.hom
    ⟨{
      hom := g
      is_mon_hom :=
        { zero_hom := F.map_injective <| by simpa [← hg, cancel_epi] using IsAddMon_Hom.zero_hom f.hom
          add_hom := F.map_injective <| by simpa [← hg, cancel_epi] using IsAddMon_Hom.add_hom f.hom }
    }, AddMon_.Hom.ext hg⟩

instance FullyFaithful.isAddMon_Hom_preimage (hF : F.FullyFaithful) {X Y : C}
    [AddMon_Class X] [AddMon_Class Y] (f : F.obj X ⟶ F.obj Y) [IsAddMon_Hom f] :
    IsAddMon_Hom (hF.preimage f) where
  zero_hom := hF.map_injective <| by simp [← obj.add_η_def_assoc, ← obj.add_η_def, ← cancel_epi (ε F)]
  add_hom := hF.map_injective <| by
    simp [← obj.add_μ_def_assoc, ← obj.add_μ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)]

/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then `Mon(F) : Mon C ⥤ Mon D` is fully
faithful too. -/
protected def FullyFaithful.mapAddMon (hF : F.FullyFaithful) : F.mapAddMon.FullyFaithful where
  preimage {X Y} f := .mk' <| hF.preimage f.hom

end Monoidal

variable (C D) in
/-- `mapAddMon` is functorial in the lax monoidal functor. -/
@[simps] -- Porting note: added this, not sure how it worked previously without.
def mapAddMonFunctor : LaxMonoidalFunctor C D ⥤ AddMon_ C ⥤ AddMon_ D where
  obj F := F.mapAddMon
  map α := { app A := .mk' (α.hom.app A.X) }
  map_comp _ _ := rfl

end Functor

open Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [a.IsMonoidal]

/-- An adjunction of monoidal functors lifts to an adjunction of their lifts to monoid objects. -/
@[simps] noncomputable def mapAddMon : F.mapAddMon ⊣ G.mapAddMon where
  unit := mapAddMonIdIso.inv ≫ mapAddMonNatTrans a.unit ≫ mapAddMonCompIso.hom
  counit := mapAddMonCompIso.inv ≫ mapAddMonNatTrans a.counit ≫ mapAddMonIdIso.hom

end Adjunction

namespace Equivalence

/-- An equivalence of categories lifts to an equivalence of their monoid objects. -/
@[simps]
noncomputable def mapAddMon (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal] :
    AddMon_ C ≌ AddMon_ D where
  functor := e.functor.mapAddMon
  inverse := e.inverse.mapAddMon
  unitIso := mapAddMonIdIso.symm ≪≫ mapAddMonNatIso e.unitIso ≪≫ mapAddMonCompIso
  counitIso := mapAddMonCompIso.symm ≪≫ mapAddMonNatIso e.counitIso ≪≫ mapAddMonIdIso

end CategoryTheory.Equivalence

namespace AddMon_

namespace EquivLaxMonoidalFunctorPUnit

variable (C) in
/-- Implementation of `AddMon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def laxMonoidalToMon : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ⥤ AddMon_ C where
  obj F := (F.mapAddMon : AddMon_ _ ⥤ AddMon_ C).obj (trivial (Discrete PUnit))
  map α := ((Functor.mapAddMonFunctor (Discrete PUnit) C).map α).app _

/-- Implementation of `AddMon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def monToLaxMonoidalObj (A : AddMon_ C) :
    Discrete PUnit.{u + 1} ⥤ C := (Functor.const _).obj A.X

instance (A : AddMon_ C) : (monToLaxMonoidalObj A).LaxMonoidal where
  ε := η[A.X]
  «μ» _ _ := μ[A.X]

@[simp]
lemma monToLaxMonoidalObj_ε (A : AddMon_ C) :
    ε (monToLaxMonoidalObj A) = η[A.X] := rfl

@[simp]
lemma monToLaxMonoidalObj_μ (A : AddMon_ C) (X Y) :
    «μ» (monToLaxMonoidalObj A) X Y = μ[A.X] := rfl

variable (C)
/-- Implementation of `AddMon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps]
def monToLaxMonoidal : AddMon_ C ⥤ LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C where
  obj A := LaxMonoidalFunctor.of (monToLaxMonoidalObj A)
  map f :=
    { hom := { app _ := f.hom }
      isMonoidal := { } }

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

/-- Implementation of `AddMon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def unitIso :
    𝟭 (LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C) ≅ laxMonoidalToMon C ⋙ monToLaxMonoidal C :=
  NatIso.ofComponents
    (fun F ↦ LaxMonoidalFunctor.isoOfComponents (fun _ ↦ F.mapIso (eqToIso (by ext))))

/-- Auxiliary definition for `counitIso`. -/
@[simps!]
def counitIsoAux (F : AddMon_ C) :
    ((monToLaxMonoidal C ⋙ laxMonoidalToMon C).obj F).X ≅ ((𝟭 (AddMon_ C)).obj F).X :=
  Iso.refl _

@[simp]
theorem monToLaxMonoidal_laxMonoidalToMon_obj_zero (F : AddMon_ C) :
    η[((monToLaxMonoidal C ⋙ laxMonoidalToMon C).obj F).X] = η[F.X] ≫ 𝟙 _ :=
  rfl

@[simp]
theorem monToLaxMonoidal_laxMonoidalToMon_obj_add (F : AddMon_ C) :
    μ[((monToLaxMonoidal C ⋙ laxMonoidalToMon C).obj F).X] = μ[F.X] ≫ 𝟙 _ :=
  rfl

theorem counitIsoAux_IsAddMon_Hom (F : AddMon_ C) :
    IsAddMon_Hom (counitIsoAux C F).hom where

/-- Implementation of `AddMon_.equivLaxMonoidalFunctorPUnit`. -/
@[simps!]
def counitIso : monToLaxMonoidal C ⋙ laxMonoidalToMon C ≅ 𝟭 (AddMon_ C) :=
  NatIso.ofComponents (fun F ↦
    letI : IsAddMon_Hom (counitIsoAux C F).hom := counitIsoAux_IsAddMon_Hom C F
    mkIso' (counitIsoAux C F))

end EquivLaxMonoidalFunctorPUnit

open EquivLaxMonoidalFunctorPUnit

attribute [local simp] eqToIso_map

/--
Monoid objects in `C` are "just" lax monoidal functors from the trivial monoidal category to `C`.
-/
@[simps]
def equivLaxMonoidalFunctorPUnit : LaxMonoidalFunctor (Discrete PUnit.{u + 1}) C ≌ AddMon_ C where
  functor := laxMonoidalToMon C
  inverse := monToLaxMonoidal C
  unitIso := unitIso C
  counitIso := counitIso C

end AddMon_

namespace AddMon_Class

/-!
In this section, we prove that the category of monoids in a braided monoidal category is monoidal.

Given two monoids `M` and `N` in a braided monoidal category `C`,
the addition on the tensor product `M.X ⊗ N.X` is defined in the obvious way:
it is the tensor product of the additions on `M` and `N`,
except that the tensor factors in the source come in the wrong order,
which we fix by pre-composing with a permutation isomorphism constructed from the braiding.

(There is a subtlety here: in fact there are two ways to do these,
using either the positive or negative crossing.)

A more conceptual way of understanding this definition is the following:
The braiding on `C` gives rise to a monoidal structure on
the tensor product functor from `C × C` to `C`.
A pair of monoids in `C` gives rise to a monoid in `C × C`,
which the tensor product functor by being monoidal takes to a monoid in `C`.
The permutation isomorphism appearing in the definition of
the addition on the tensor product of two monoids is
an instance of a more general family of isomorphisms
which together form a strength that equips the tensor product functor with a monoidal structure,
and the monoid axioms for the tensor product follow from the monoid axioms for the tensor factors
plus the properties of the strength (i.e., monoidal functor axioms).
The strength `tensorμ` of the tensor product functor has been defined in
`Mathlib/CategoryTheory/Monoidal/Braided.lean`.
Its properties, stated as independent lemmas in that module,
are used extensively in the proofs below.
Notice that we could have followed the above plan not only conceptually
but also as a possible implementation and
could have constructed the tensor product of monoids via `mapAddMon`,
but we chose to give a more explicit definition directly in terms of `tensorμ`.

To complete the definition of the monoidal category structure on the category of monoids,
we need to provide definitions of associator and unitors.
The obvious candidates are the associator and unitors from `C`,
but we need to prove that they are monoid morphisms, i.e., compatible with unit and addition.
These properties translate to the monoidality of the associator and unitors
(with respect to the monoidal structures on the functors they relate),
which have also been proved in `Mathlib/CategoryTheory/Monoidal/Braided.lean`.

-/

-- The proofs that associators and unitors preserve monoid units don't require braiding.
theorem zero_associator {M N P : C} [AddMon_Class M] [AddMon_Class N] [AddMon_Class P] :
    ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ η[N]) ⊗ₘ η[P])) ≫ (α_ M N P).hom =
      (λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ (λ_ (𝟙_ C)).inv ≫ (η[N] ⊗ₘ η[P])) := by
  simp only [Category.assoc, Iso.cancel_iso_inv_left]
  slice_lhs 1 3 => rw [← Category.id_comp (η : 𝟙_ C ⟶ P), tensor_comp]
  slice_lhs 2 3 => rw [associator_naturality]
  slice_rhs 1 2 => rw [← Category.id_comp η, tensor_comp]
  slice_lhs 1 2 => rw [tensorHom_id, ← leftUnitor_tensor_inv]
  rw [← cancel_epi (λ_ (𝟙_ C)).inv]
  slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
  simp

theorem zero_leftUnitor {M : C} [AddMon_Class M] :
    ((λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ η[M])) ≫ (λ_ M).hom = η := by
  simp

theorem zero_rightUnitor {M : C} [AddMon_Class M] :
    ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ 𝟙 (𝟙_ C))) ≫ (ρ_ M).hom = η := by
  simp [← unitors_equal]

section BraidedCategory

variable [BraidedCategory C]

theorem AddMon_tensor_zero_add (M N : C) [AddMon_Class M] [AddMon_Class N] :
    (((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ η[N])) ▷ (M ⊗ N)) ≫
        tensorμ M N M N ≫ (μ ⊗ₘ μ) =
      (λ_ (M ⊗ N)).hom := by
  simp only [comp_whiskerRight_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [← tensor_comp, zero_add, zero_add]
  symm
  exact tensor_left_unitality M N

theorem AddMon_tensor_add_zero (M N : C) [AddMon_Class M] [AddMon_Class N] :
    (M ⊗ N) ◁ ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ η[N])) ≫
        tensorμ M N M N ≫ (μ[M] ⊗ₘ μ[N]) =
      (ρ_ (M ⊗ N)).hom := by
  simp only [whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_right]
  slice_lhs 3 4 => rw [← tensor_comp, add_zero, add_zero]
  symm
  exact tensor_right_unitality M N

theorem AddMon_tensor_add_assoc (M N : C) [AddMon_Class M] [AddMon_Class N] :
    ((tensorμ M N M N ≫ (μ ⊗ₘ μ)) ▷ (M ⊗ N)) ≫
        tensorμ M N M N ≫ (μ ⊗ₘ μ) =
      (α_ (M ⊗ N : C) (M ⊗ N) (M ⊗ N)).hom ≫
        ((M ⊗ N : C) ◁ (tensorμ M N M N ≫ (μ ⊗ₘ μ))) ≫
          tensorμ M N M N ≫ (μ ⊗ₘ μ) := by
  simp only [comp_whiskerRight_assoc, whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [← tensor_comp, add_assoc, add_assoc, tensor_comp, tensor_comp]
  slice_lhs 1 3 => rw [tensor_associativity]
  slice_lhs 3 4 => rw [← tensorμ_natural_right]
  simp

theorem add_associator {M N P : C} [AddMon_Class M] [AddMon_Class N] [AddMon_Class P] :
    (tensorμ (M ⊗ N) P (M ⊗ N) P ≫
          (tensorμ M N M N ≫ (μ ⊗ₘ μ) ⊗ₘ μ)) ≫
        (α_ M N P).hom =
      ((α_ M N P).hom ⊗ₘ (α_ M N P).hom) ≫
        tensorμ M (N ⊗ P) M (N ⊗ P) ≫
          (μ ⊗ₘ tensorμ N P N P ≫ (μ ⊗ₘ μ)) := by
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← Category.id_comp μ[P], tensor_comp]
  slice_lhs 3 4 => rw [associator_naturality]
  slice_rhs 3 4 => rw [← Category.id_comp μ, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 1 3 => rw [associator_monoidal]
  simp only [Category.assoc]

theorem add_leftUnitor {M : C} [AddMon_Class M] :
    (tensorμ (𝟙_ C) M (𝟙_ C) M ≫ ((λ_ (𝟙_ C)).hom ⊗ₘ μ)) ≫ (λ_ M).hom =
      ((λ_ M).hom ⊗ₘ (λ_ M).hom) ≫ μ := by
  rw [← Category.comp_id (λ_ (𝟙_ C)).hom, ← Category.id_comp μ, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 1 3 => rw [← leftUnitor_monoidal]
  simp only [Category.id_comp]

theorem add_rightUnitor {M : C} [AddMon_Class M] :
    (tensorμ M (𝟙_ C) M (𝟙_ C) ≫ (μ ⊗ₘ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ M).hom =
      ((ρ_ M).hom ⊗ₘ (ρ_ M).hom) ≫ μ := by
  rw [← Category.id_comp μ, ← Category.comp_id (λ_ (𝟙_ C)).hom, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  slice_lhs 1 3 => rw [← rightUnitor_monoidal]
  simp only [Category.id_comp]

namespace tensorObj

-- We don't want `tensorObj.zero_def` to be simp as it would loop with `IsAddMon_Hom.zero_hom` applied
-- to `(λ_ N.X).inv`.
@[simps -isSimp]
instance {M N : C} [AddMon_Class M] [AddMon_Class N] : AddMon_Class (M ⊗ N) where
  zero := (λ_ (𝟙_ C)).inv ≫ (η ⊗ₘ η)
  add := tensorμ M N M N ≫ (μ ⊗ₘ μ)
  zero_add := AddMon_tensor_zero_add M N
  add_zero := AddMon_tensor_add_zero M N
  add_assoc := AddMon_tensor_add_assoc M N

end tensorObj

open IsAddMon_Hom

variable {X Y Z W : C} [AddMon_Class X] [AddMon_Class Y] [AddMon_Class Z] [AddMon_Class W]

instance {f : X ⟶ Y} {g : Z ⟶ W} [IsAddMon_Hom f] [IsAddMon_Hom g] : IsAddMon_Hom (f ⊗ₘ g) where
  zero_hom := by
    dsimp [tensorObj.zero_def]
    slice_lhs 2 3 => rw [← tensor_comp, zero_hom, zero_hom]
  add_hom := by
    dsimp [tensorObj.add_def]
    slice_rhs 1 2 => rw [tensorμ_natural]
    slice_lhs 2 3 => rw [← tensor_comp, add_hom, add_hom, tensor_comp]
    simp only [Category.assoc]

instance : IsAddMon_Hom (𝟙 X) where

instance {f : Y ⟶ Z} [IsAddMon_Hom f] : IsAddMon_Hom (X ◁ f) where
  zero_hom := by simpa using (inferInstanceAs <| IsAddMon_Hom (𝟙 X ⊗ₘ f)).zero_hom
  add_hom := by simpa using (inferInstanceAs <| IsAddMon_Hom (𝟙 X ⊗ₘ f)).add_hom

instance {f : X ⟶ Y} [IsAddMon_Hom f] : IsAddMon_Hom (f ▷ Z) where
  zero_hom := by simpa using (inferInstanceAs <| IsAddMon_Hom (f ⊗ₘ (𝟙 Z))).zero_hom
  add_hom := by simpa using (inferInstanceAs <| IsAddMon_Hom (f ⊗ₘ (𝟙 Z))).add_hom

instance : IsAddMon_Hom (α_ X Y Z).hom :=
  ⟨zero_associator, add_associator⟩

instance : IsAddMon_Hom (λ_ X).hom :=
  ⟨zero_leftUnitor, add_leftUnitor⟩

instance : IsAddMon_Hom (ρ_ X).hom :=
  ⟨zero_rightUnitor, add_rightUnitor⟩

theorem zero_braiding (X Y : C) [AddMon_Class X] [AddMon_Class Y] : η ≫ (β_ X Y).hom = η := by
  simp only [tensorObj.zero_def, Category.assoc, BraidedCategory.braiding_naturality,
    braiding_tensorUnit_right, Iso.cancel_iso_inv_left]
  monoidal

end BraidedCategory

end AddMon_Class

namespace AddMon_

section BraidedCategory

variable [BraidedCategory C]

@[simps! tensorObj_X tensorHom_hom]
instance addMonMonoidalStruct : MonoidalCategoryStruct (AddMon_ C) where
  tensorObj M N := ⟨M.X ⊗ N.X⟩
  tensorHom f g := Hom.mk (f.hom ⊗ₘ g.hom)
  whiskerRight f Y := Hom.mk (f.hom ▷ Y.X)
  whiskerLeft X _ _ g := Hom.mk (X.X ◁ g.hom)
  tensorUnit := ⟨𝟙_ C⟩
  associator M N P := mkIso' <| associator M.X N.X P.X
  leftUnitor M := mkIso' <| leftUnitor M.X
  rightUnitor M := mkIso' <| rightUnitor M.X

@[simp]
theorem tensorUnit_X : (𝟙_ (AddMon_ C)).X = 𝟙_ C := rfl

@[simp]
theorem tensorUnit_zero : η[(𝟙_ (AddMon_ C)).X] = 𝟙 (𝟙_ C) := rfl

@[simp]
theorem tensorUnit_add : μ[(𝟙_ (AddMon_ C)).X] = (λ_ (𝟙_ C)).hom := rfl

@[simp]
theorem tensorObj_zero (X Y : AddMon_ C) : η[(X ⊗ Y).X] = (λ_ (𝟙_ C)).inv ≫ (η[X.X] ⊗ₘ η[Y.X]) := rfl

@[simp]
theorem tensorObj_add (X Y : AddMon_ C) :
    μ[(X ⊗ Y).X] = tensorμ X.X Y.X X.X Y.X ≫ (μ[X.X] ⊗ₘ μ[Y.X]) := rfl

@[simp]
theorem whiskerLeft_hom {X Y : AddMon_ C} (f : X ⟶ Y) (Z : AddMon_ C) :
    (f ▷ Z).hom = f.hom ▷ Z.X := by
  rfl

@[simp]
theorem whiskerRight_hom (X : AddMon_ C) {Y Z : AddMon_ C} (f : Y ⟶ Z) :
    (X ◁ f).hom = X.X ◁ f.hom := by
  rfl

@[simp]
theorem leftUnitor_hom_hom (X : AddMon_ C) : (λ_ X).hom.hom = (λ_ X.X).hom := rfl

@[simp]
theorem leftUnitor_inv_hom (X : AddMon_ C) : (λ_ X).inv.hom = (λ_ X.X).inv := rfl

@[simp]
theorem rightUnitor_hom_hom (X : AddMon_ C) : (ρ_ X).hom.hom = (ρ_ X.X).hom := rfl

@[simp]
theorem rightUnitor_inv_hom (X : AddMon_ C) : (ρ_ X).inv.hom = (ρ_ X.X).inv := rfl

@[simp]
theorem associator_hom_hom (X Y Z : AddMon_ C) : (α_ X Y Z).hom.hom = (α_ X.X Y.X Z.X).hom := rfl

@[simp]
theorem associator_inv_hom (X Y Z : AddMon_ C) : (α_ X Y Z).inv.hom = (α_ X.X Y.X Z.X).inv := rfl

@[simp]
theorem tensor_zero (M N : AddMon_ C) : η[(M ⊗ N).X] = (λ_ (𝟙_ C)).inv ≫ (η[M.X] ⊗ₘ η[N.X]) := rfl

@[simp]
theorem tensor_add (M N : AddMon_ C) : μ[(M ⊗ N).X] =
    tensorμ M.X N.X M.X N.X ≫ (μ[M.X] ⊗ₘ μ[N.X]) := rfl

instance monMonoidal : MonoidalCategory (AddMon_ C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]

-- We don't want `tensorObj.zero_def` to be simp as it would loop with `IsAddMon_Hom.zero_hom` applied
-- to `(λ_ N.X).inv`.
@[simps! -isSimp]
instance {M N : C} [AddMon_Class M] [AddMon_Class N] : AddMon_Class (M ⊗ N) :=
  inferInstanceAs <| AddMon_Class (AddMon_.mk M ⊗ AddMon_.mk N).X

variable (C)

/-- The forgetful functor from `AddMon_ C` to `C` is monoidal when `C` is monoidal. -/
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

@[simp] theorem forget_ε : ε (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_η : «η» (forget C) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_μ (X Y : AddMon_ C) : «μ» (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl
@[simp] theorem forget_δ (X Y : AddMon_ C) : δ (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl

end BraidedCategory

end AddMon_

/-!
We next show that if `C` is symmetric, then `AddMon_ C` is braided, and indeed symmetric.

Note that `AddMon_ C` is *not* braided in general when `C` is only braided.

The more interesting construction is the 2-category of monoids in `C`,
bimodules between the monoids, and intertwiners between the bimodules.

When `C` is braided, that is a monoidal 2-category.
-/
section SymmetricCategory

variable [SymmetricCategory C]

namespace AddMon_Class

theorem add_braiding (X Y : C) [AddMon_Class X] [AddMon_Class Y] :
    μ ≫ (β_ X Y).hom = ((β_ X Y).hom ⊗ₘ (β_ X Y).hom) ≫ μ := by
  dsimp [tensorObj.add_def]
  simp only [tensorμ, Category.assoc, BraidedCategory.braiding_naturality,
    BraidedCategory.braiding_tensor_right_hom, BraidedCategory.braiding_tensor_left_hom,
    comp_whiskerRight, whisker_assoc, whiskerLeft_comp, pentagon_assoc,
    pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
  slice_lhs 3 4 =>
    -- We use symmetry here:
    rw [← whiskerLeft_comp, ← comp_whiskerRight, SymmetricCategory.symmetry]
  simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.assoc, pentagon_inv_assoc,
    Iso.hom_inv_id_assoc]
  slice_lhs 1 2 =>
    rw [← associator_inv_naturality_left]
  slice_lhs 2 3 =>
    rw [Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 2 3 =>
    rw [← associator_naturality_right]
  slice_lhs 1 2 =>
    rw [← tensorHom_def]
  simp only [Category.assoc]

instance {X Y : C} [AddMon_Class X] [AddMon_Class Y] : IsAddMon_Hom (β_ X Y).hom :=
  ⟨zero_braiding X Y, add_braiding X Y⟩

end AddMon_Class

namespace AddMon_

instance : SymmetricCategory (AddMon_ C) where
  braiding X Y := mkIso' (β_ X.X Y.X)
  symmetry X Y := by
    ext
    simp

end AddMon_

end SymmetricCategory

section

variable [BraidedCategory.{v₁} C]

/-- Predicate for a monoid object to be commutative. -/
class IsAddCommMon (X : C) [AddMon_Class X] where
  add_comm (X) : (β_ X X).hom ≫ μ = μ := by aesop_cat

open scoped AddMon_Class

namespace IsAddCommMon

attribute [reassoc (attr := simp)] add_comm

instance : IsAddCommMon (𝟙_ C) where
  add_comm := by dsimp; rw [braiding_leftUnitor, unitors_equal]

end IsAddCommMon

end
