/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Michail Karatarakis
-/
import PolyML.Monoidal.Vect
import PolyML.Monoidal.FreeAddCommMon
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Bags in `Vect k`

Parallel to `PolyML.Monoidal.BagInType` for `Type u`, this file constructs bags
(free commutative monoid objects) in `Vect k`.

The bag object on `V` is the symmetric algebra `Sym(V)`, the free commutative `k`-algebra on `V`.
Aggregation into the feature space `V` is modeled by morphisms `bag V ⟶ V` from internal
commutative monoids.
-/

universe u

namespace CategoryTheory

open MonoidalCategory ModuleCat SymmetricAlgebra AddMonObj AddMon AddCommMon LinearMap
open scoped AddMonObj TensorProduct

namespace Vect

variable {k : Type u} [Field k]

/-- Symmetric algebra of the carrier of `V`, as an object of `Vect k`. -/
noncomputable abbrev symObj (V : Vect k) : Vect k :=
  ModuleCat.of k (SymmetricAlgebra k V.carrier)

/-- Bag object on `V` in `Vect k`. -/
noncomputable abbrev bagObj (V : Vect k) : Vect k := symObj V

/-- Canonical linear inclusion `V → Sym(V)`. -/
noncomputable def bagι (V : Vect k) : V ⟶ bagObj V :=
  ModuleCat.ofHom (SymmetricAlgebra.ι k V.carrier)

@[simp]
theorem bagι_apply (V : Vect k) (v : V.carrier) :
    (bagι V).hom v = SymmetricAlgebra.ι k V.carrier v := rfl

/-- The feature space into which multisets of vectors in `V` are aggregated. -/
def aggregationTarget (V : Vect k) : Vect k := V

/-- Unit of the internal commutative monoid on `Sym(V)`. -/
noncomputable def symZero (V : Vect k) : 𝟙_ (Vect k) ⟶ symObj V :=
  ModuleCat.ofHom (Algebra.linearMap k (SymmetricAlgebra k V.carrier))

/-- Multiplication of the internal commutative monoid on `Sym(V)`. -/
noncomputable def symAdd (V : Vect k) : symObj V ⊗ symObj V ⟶ symObj V :=
  ModuleCat.ofHom (LinearMap.mul' k (SymmetricAlgebra k V.carrier))

theorem symZero_add (V : Vect k) :
    symZero V ▷ symObj V ≫ symAdd V = (λ_ (symObj V)).hom := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro r m
  show (LinearMap.mul' k (SymmetricAlgebra k V.carrier))
      (((Algebra.linearMap k (SymmetricAlgebra k V.carrier)).rTensor _) (r ⊗ₜ m)) =
    (TensorProduct.lid k (SymmetricAlgebra k V.carrier)).toLinearMap (r ⊗ₜ m)
  simp [LinearMap.mul'_apply, LinearMap.rTensor_tmul, Algebra.smul_def, TensorProduct.lid_tmul]

theorem symAdd_zero (V : Vect k) :
    symObj V ◁ symZero V ≫ symAdd V = (ρ_ (symObj V)).hom := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m r
  show (LinearMap.mul' k (SymmetricAlgebra k V.carrier))
      (((Algebra.linearMap k (SymmetricAlgebra k V.carrier)).lTensor _) (m ⊗ₜ r)) =
    (TensorProduct.rid k (SymmetricAlgebra k V.carrier)).toLinearMap (m ⊗ₜ r)
  simp [LinearMap.mul'_apply, LinearMap.lTensor_tmul, Algebra.smul_def, TensorProduct.rid_tmul, mul_comm]

theorem symAdd_assoc (V : Vect k) :
    symAdd V ▷ symObj V ≫ symAdd V =
      (α_ (symObj V) (symObj V) (symObj V)).hom ≫ symObj V ◁ symAdd V ≫ symAdd V := by
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro a b c
  show (LinearMap.mul' k (SymmetricAlgebra k V.carrier))
      (((LinearMap.mul' k (SymmetricAlgebra k V.carrier)).rTensor _) ((a ⊗ₜ b) ⊗ₜ c)) =
    (LinearMap.mul' k (SymmetricAlgebra k V.carrier))
      (((LinearMap.mul' k (SymmetricAlgebra k V.carrier)).lTensor _)
        ((TensorProduct.assoc k (SymmetricAlgebra k V.carrier) (SymmetricAlgebra k V.carrier)
          (SymmetricAlgebra k V.carrier)) ((a ⊗ₜ b) ⊗ₜ c)))
  rw [LinearMap.rTensor_tmul, LinearMap.mul'_apply]
  conv_rhs => arg 2; rw [TensorProduct.assoc_tmul]
  rw [LinearMap.lTensor_tmul, LinearMap.mul'_apply]
  exact mul_assoc a b c

theorem symAdd_comm (V : Vect k) :
    (β_ (symObj V) (symObj V)).hom ≫ symAdd V = symAdd V := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  show (LinearMap.mul' k (SymmetricAlgebra k V.carrier))
      ((TensorProduct.comm k _ _).toLinearMap (a ⊗ₜ b)) =
    (LinearMap.mul' k (SymmetricAlgebra k V.carrier)) (a ⊗ₜ b)
  simp [LinearMap.mul'_apply, LinearMap.mul'_comm, TensorProduct.comm_tmul, mul_comm]

noncomputable instance symAddMonObj (V : Vect k) : AddMonObj (symObj V) where
  zero := symZero V
  add := symAdd V
  zero_add := symZero_add V
  add_zero := symAdd_zero V
  add_assoc := symAdd_assoc V

@[simp]
theorem η_symObj (V : Vect k) : η[symObj V] = symZero V := rfl

@[simp]
theorem symZero_apply (V : Vect k) (r : k) :
    (symZero V).hom r = algebraMap k (SymmetricAlgebra k V.carrier) r := rfl

@[simp]
theorem symAdd_apply (V : Vect k) (a b : SymmetricAlgebra k V.carrier) :
    (symAdd V).hom (a ⊗ₜ[k] b) = a * b := rfl

@[simp]
theorem μ_symObj (V : Vect k) : μ[symObj V] = symAdd V := rfl

noncomputable instance symIsAddCommMonObj (V : Vect k) : IsAddCommMonObj (symObj V) where
  add_comm := symAdd_comm V

/-- The free commutative monoid object on `V` in `Vect k`. -/
noncomputable def symAddCommMon (V : Vect k) : AddCommMon (Vect k) :=
  { X := symObj V }

@[simp]
theorem symAddCommMon_X (V : Vect k) : (symAddCommMon V).X = symObj V := rfl

theorem comp_hom_apply {A B C : Vect k} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (f ≫ g).hom x = g.hom (f.hom x) := ModuleCat.comp_apply f g x

@[simp]
theorem ofHom_hom {A B : Vect k} (f : A.carrier →ₗ[k] B.carrier) :
    (ModuleCat.ofHom f).hom = f := rfl

theorem ofHom_comp_apply {A B C : Vect k} (f : A ⟶ B) (g : B.carrier →ₗ[k] C.carrier) (x : A) :
    (f ≫ ModuleCat.ofHom g).hom x = g (f.hom x) := by
  simp [ModuleCat.comp_apply, ofHom_hom]

namespace addCommMonAlgebra

variable {M : AddCommMon (Vect k)}

/-- Carrier multiplication induced by the internal monoid structure on `M.X`. -/
noncomputable def addCommMonMul (a b : M.X) : M.X :=
  (μ[M.X]).hom (a ⊗ₜ[k] b)

@[simp]
theorem addCommMonMul_apply (a b : M.X) :
    addCommMonMul (M := M) a b = (μ[M.X]).hom (a ⊗ₜ b) := rfl

theorem addCommMonMul_one_mul (a : M.X) :
    addCommMonMul (M := M) ((η[M.X]).hom 1) a = a := by
  change ((η[M.X] ⊗ₘ 𝟙 M.X) ≫ μ[M.X]) (1 ⊗ₜ[k] a) = a
  rw [AddMonObj.one_mul_hom, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply, one_smul, ModuleCat.id_apply]

theorem addCommMonMul_mul_one (a : M.X) :
    addCommMonMul (M := M) a ((η[M.X]).hom 1) = a := by
  change ((𝟙 M.X ⊗ₘ η[M.X]) ≫ μ[M.X]) (a ⊗ₜ[k] 1) = a
  rw [AddMonObj.mul_zero_hom, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_hom_apply, one_smul, ModuleCat.id_apply]

theorem addCommMonMul_assoc (a b c : M.X) :
    addCommMonMul (M := M) (addCommMonMul a b) c =
      addCommMonMul a (addCommMonMul b c) := by
  rw [addCommMonMul_apply, addCommMonMul_apply]
  show ((μ[M.X] ▷ M.X) ≫ μ[M.X]) ((a ⊗ₜ[k] b) ⊗ₜ[k] c) =
    ((M.X ◁ μ[M.X]) ≫ μ[M.X]) (a ⊗ₜ[k] (b ⊗ₜ[k] c))
  rw [AddMonObj.add_assoc M.X, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.associator_hom_apply, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply]

theorem addCommMonMul_comm (a b : M.X) :
    addCommMonMul (M := M) a b = addCommMonMul b a := by
  rw [addCommMonMul_apply, addCommMonMul_apply]
  have h := IsAddCommMonObj.add_comm (X := M.X)
  have hβ : (β_ M.X M.X).hom (a ⊗ₜ[k] b) = b ⊗ₜ[k] a := by
    simp [ModuleCat.MonoidalCategory.braiding_hom_apply]
  calc (μ[M.X]).hom (a ⊗ₜ[k] b)
      _ = (μ[M.X]).hom ((β_ M.X M.X).hom (a ⊗ₜ[k] b)) := by
        rw [← comp_hom_apply (β_ M.X M.X).hom (μ[M.X]), h]
      _ = (μ[M.X]).hom (b ⊗ₜ[k] a) := by rw [hβ]

theorem eta_mul (r s : k) :
    (η[M.X]).hom (r * s) = addCommMonMul (M := M) ((η[M.X]).hom r) ((η[M.X]).hom s) := by
  have hη : IsAddMonHom (η[M.X] : 𝟙_ (Vect k) ⟶ M.X) :=
    (AddMon.uniqueHomFromTrivial (AddCommMon.toAddMon M)).default.isMonHom_hom
  have hμ : (μ[𝟙_ (Vect k)]).hom (r ⊗ₜ[k] s) = r * s := by
    simp [AddMon.tensorUnit_mul, ModuleCat.MonoidalCategory.leftUnitor_hom_apply, one_smul]
  rw [addCommMonMul_apply, ← hμ, ← comp_hom_apply (μ[𝟙_ (Vect k)]) (η[M.X]), hη.add_hom,
    comp_hom_apply (η[M.X] ⊗ₘ η[M.X]) (μ[M.X])]
  simp only [ModuleCat.MonoidalCategory.tensorHom_tmul, addCommMonMul_apply]

theorem eta_smul (r : k) (a : M.X) :
    addCommMonMul (M := M) ((η[M.X]).hom r) a = r • a := by
  change ((η[M.X] ▷ M.X) ≫ μ[M.X]) (r ⊗ₜ[k] a) = r • a
  rw [AddMonObj.zero_add M.X, ModuleCat.MonoidalCategory.leftUnitor_hom_apply]

theorem hom_map_mul {M₀ N₀ : AddCommMon (Vect k)} (f : M₀ ⟶ N₀) (a b : M₀.X) :
    f.hom (addCommMonMul (M := M₀) a b) = addCommMonMul (M := N₀) (f.hom a) (f.hom b) := by
  rw [addCommMonMul_apply, addCommMonMul_apply]
  show ((μ[M₀.X]) ≫ f.hom).hom (a ⊗ₜ[k] b) = (μ[N₀.X]).hom (f.hom a ⊗ₜ[k] f.hom b)
  rw [f.isMonHom_hom.add_hom, ModuleCat.comp_apply]
  exact congrArg (μ[N₀.X]).hom (ModuleCat.MonoidalCategory.tensorHom_tmul f.hom f.hom a b)

theorem addCommMonMul_zero_mul (a : M.X) :
    addCommMonMul (M := M) 0 a = 0 := by
  rw [addCommMonMul_apply, TensorProduct.zero_tmul, map_zero (μ[M.X]).hom]

theorem addCommMonMul_mul_zero (a : M.X) :
    addCommMonMul (M := M) a 0 = 0 := by
  rw [addCommMonMul_apply, TensorProduct.tmul_zero, map_zero (μ[M.X]).hom]

theorem addCommMonMul_left_distrib (a b c : M.X) :
    addCommMonMul (M := M) (a + b) c = addCommMonMul a c + addCommMonMul b c := by
  rw [addCommMonMul_apply, TensorProduct.add_tmul, map_add (μ[M.X]).hom, addCommMonMul_apply,
    addCommMonMul_apply]

theorem addCommMonMul_right_distrib (a b c : M.X) :
    addCommMonMul (M := M) a (b + c) = addCommMonMul a b + addCommMonMul a c := by
  rw [addCommMonMul_apply, TensorProduct.tmul_add, map_add (μ[M.X]).hom, addCommMonMul_apply,
    addCommMonMul_apply]

/-- Semiring structure on the carrier of an internal commutative monoid in `Vect k`. -/
noncomputable instance addCommMonCarrierSemiring : Semiring M.X.carrier where
  __ := inferInstanceAs (AddCommMonoid M.X.carrier)
  mul := addCommMonMul (M := M)
  one := (η[M.X]).hom 1
  zero_mul := addCommMonMul_zero_mul
  mul_zero := addCommMonMul_mul_zero
  mul_one := addCommMonMul_mul_one
  one_mul := addCommMonMul_one_mul
  mul_assoc := addCommMonMul_assoc
  left_distrib := addCommMonMul_right_distrib
  right_distrib := addCommMonMul_left_distrib

/-- Commutative semiring structure on the carrier of an internal commutative monoid in `Vect k`. -/
noncomputable instance addCommMonCarrierCommSemiring : CommSemiring M.X.carrier where
  __ := addCommMonCarrierSemiring (M := M)
  mul_comm := addCommMonMul_comm

/-- The canonical ring homomorphism `k →+* M.X` from the internal unit. -/
noncomputable def addCommMonCarrierRingHom : k →+* M.X.carrier where
  toFun := (η[M.X]).hom
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := rfl
  map_mul' r s := eta_mul (M := M) r s

/-- Algebra structure on the carrier of an internal commutative monoid in `Vect k`. -/
noncomputable instance addCommMonCarrierAlgebra : Algebra k M.X.carrier where
  __ := addCommMonCarrierSemiring (M := M)
  algebraMap := addCommMonCarrierRingHom
  commutes' r x := addCommMonMul_comm (M := M) (addCommMonCarrierRingHom r) x
  smul_def' r a := (eta_smul (M := M) r a).symm

end addCommMonAlgebra

namespace addCommMonCarrier

open addCommMonAlgebra

variable {M : AddCommMon (Vect k)}

noncomputable instance instSemiring : Semiring M.X.carrier :=
  addCommMonCarrierSemiring (M := M)

noncomputable instance instCommSemiring : CommSemiring M.X.carrier :=
  addCommMonCarrierCommSemiring (M := M)

noncomputable instance instAlgebra : Algebra k M.X.carrier :=
  addCommMonCarrierAlgebra (M := M)

end addCommMonCarrier

attribute [instance] addCommMonCarrier.instSemiring addCommMonCarrier.instCommSemiring
  addCommMonCarrier.instAlgebra

/-- Multiplication on `Sym(V)` is the carrier algebra multiplication. -/
theorem symAddCommMon_mul {V : Vect k} (a b : SymmetricAlgebra k V.carrier) :
    addCommMonAlgebra.addCommMonMul (M := symAddCommMon V) a b = a * b := by
  rw [addCommMonAlgebra.addCommMonMul_apply, μ_symObj V]
  exact symAdd_apply V a b

theorem addCommMonHom_map_mul {M₀ N₀ : AddCommMon (Vect k)} (f : M₀ ⟶ N₀) (a b : M₀.X) :
    f.hom (addCommMonAlgebra.addCommMonMul (M := M₀) a b) =
      addCommMonAlgebra.addCommMonMul (M := N₀) (f.hom a) (f.hom b) :=
  addCommMonAlgebra.hom_map_mul f a b

@[simp]
theorem addCommMonMul_eq_mul {M : AddCommMon (Vect k)} (a b : M.X) :
    addCommMonAlgebra.addCommMonMul (M := M) a b = a * b := rfl

theorem symMapAlg_zero_hom {V W : Vect k} (f : V ⟶ W)
    (liftAlg : SymmetricAlgebra k V.carrier →ₐ[k] (bagObj W).carrier) :
    η[symObj V] ≫ ModuleCat.ofHom liftAlg.toLinearMap = η[symObj W] := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  rw [comp_hom_apply (η[symObj V]) (ModuleCat.ofHom liftAlg.toLinearMap), η_symObj V,
    symZero_apply V r]
  change (liftAlg (algebraMap k (SymmetricAlgebra k V.carrier) r)) =
    (η[symObj W]).hom r
  rw [AlgHom.commutes liftAlg r, ← symZero_apply W r, ← η_symObj W]

theorem symMapAlg_add_hom {V W : Vect k} (_f : V ⟶ W)
    (liftAlg : SymmetricAlgebra k V.carrier →ₐ[k] (bagObj W).carrier) :
    μ[symObj V] ≫ ModuleCat.ofHom liftAlg.toLinearMap =
      (ModuleCat.ofHom liftAlg.toLinearMap ⊗ₘ ModuleCat.ofHom liftAlg.toLinearMap) ≫ μ[symObj W] := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  simp only [comp_hom_apply, symAdd_apply, ModuleCat.MonoidalCategory.tensorHom_tmul]
  exact map_mul liftAlg a b

theorem symLift_zero_hom {V : Vect k} {N : AddCommMon (Vect k)} (_f : V ⟶ N.X)
    (liftAlg : SymmetricAlgebra k V.carrier →ₐ[k] N.X.carrier) :
    η[symObj V] ≫ ModuleCat.ofHom liftAlg.toLinearMap = η[N.X] := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  rw [comp_hom_apply (η[symObj V]) (ModuleCat.ofHom liftAlg.toLinearMap), η_symObj V,
    symZero_apply V r]
  change (liftAlg (algebraMap k (SymmetricAlgebra k V.carrier) r)) = (η[N.X]).hom r
  rw [AlgHom.commutes liftAlg r]
  rfl

theorem symLift_add_hom {V : Vect k} {N : AddCommMon (Vect k)} (_f : V ⟶ N.X)
    (liftAlg : SymmetricAlgebra k V.carrier →ₐ[k] N.X.carrier) :
    μ[symObj V] ≫ ModuleCat.ofHom liftAlg.toLinearMap =
      (ModuleCat.ofHom liftAlg.toLinearMap ⊗ₘ ModuleCat.ofHom liftAlg.toLinearMap) ≫ μ[N.X] := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  simp only [comp_hom_apply, symAdd_apply, ModuleCat.MonoidalCategory.tensorHom_tmul]
  exact map_mul liftAlg a b

/-- Linear map into the carrier algebra, retyped for `SymmetricAlgebra.lift`. -/
noncomputable def symLiftLinearMap {V : Vect k} {N : AddCommMon (Vect k)} (f : V ⟶ N.X) :
    @LinearMap k k CommSemiring.toSemiring CommSemiring.toSemiring (RingHom.id k) V.carrier N.X.carrier
      inferInstance inferInstance inferInstance Algebra.toModule := by
  classical
  letI : Algebra k N.X.carrier := addCommMonCarrier.instAlgebra (M := N)
  exact (AlgHom.id k N.X.carrier).toLinearMap.comp f.hom

noncomputable def symLiftAlg {V : Vect k} {N : AddCommMon (Vect k)} (f : V ⟶ N.X) :
    SymmetricAlgebra k V.carrier →ₐ[k] N.X.carrier :=
  SymmetricAlgebra.lift ((AlgHom.id k N.X.carrier).toLinearMap.comp f.hom)

noncomputable def symLift {V : Vect k} {N : AddCommMon (Vect k)} (f : V ⟶ N.X) :
    symAddCommMon V ⟶ N :=
  let liftAlg := symLiftAlg f
  AddMon.Hom.mk' (ModuleCat.ofHom liftAlg.toLinearMap)
    (symLift_zero_hom f liftAlg) (symLift_add_hom f liftAlg)

@[simp]
theorem symLiftAlg_ι {V : Vect k} {N : AddCommMon (Vect k)} (f : V ⟶ N.X) (v : V.carrier) :
    symLiftAlg f (SymmetricAlgebra.ι k V.carrier v) = f.hom v := by
  show SymmetricAlgebra.lift ((AlgHom.id k N.X.carrier).toLinearMap.comp f.hom)
      (SymmetricAlgebra.ι k V.carrier v) = f.hom v
  rw [SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply]
  simp [AlgHom.toLinearMap_id]

/-- Extend a linear map into a symmetric algebra, as an internal monoid homomorphism. -/
noncomputable def symMapAlg {V W : Vect k} (f : V ⟶ W) : symAddCommMon V ⟶ symAddCommMon W :=
  let liftAlg : SymmetricAlgebra k V.carrier →ₐ[k] (bagObj W).carrier :=
    SymmetricAlgebra.lift ((bagι W).hom.comp f.hom)
  AddMon.Hom.mk' (ModuleCat.ofHom liftAlg.toLinearMap)
    (symMapAlg_zero_hom f liftAlg) (symMapAlg_add_hom f liftAlg)

@[simp]
theorem symMapAlg_apply_lift {U V : Vect k} (f : U ⟶ V) (x : SymmetricAlgebra k U.carrier) :
    (symMapAlg f).hom x = SymmetricAlgebra.lift ((bagι V).hom.comp f.hom) x := by
  simp [symMapAlg]

@[simp]
theorem symMapAlg_ι {U V : Vect k} (f : U ⟶ V) (v : U.carrier) :
    (symMapAlg f).hom (SymmetricAlgebra.ι k U.carrier v) = (bagι V).hom (f.hom v) := by
  show SymmetricAlgebra.lift ((bagι V).hom.comp f.hom) (SymmetricAlgebra.ι k U.carrier v) =
      (bagι V).hom (f.hom v)
  rw [SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply, bagι_apply]

theorem symMapAlg_hom_map_mul {U V : Vect k} (f : U ⟶ V) (a b : SymmetricAlgebra k U.carrier) :
    (symMapAlg f).hom (a * b) =
      (SymmetricAlgebra.lift ((bagι V).hom.comp f.hom)) a *
        (SymmetricAlgebra.lift ((bagι V).hom.comp f.hom)) b := by
  dsimp [symMapAlg]
  exact map_mul (SymmetricAlgebra.lift ((bagι V).hom.comp f.hom)) a b

theorem symMapAlg_hom_map_add {U V : Vect k} (f : U ⟶ V) (a b : SymmetricAlgebra k U.carrier) :
    (symMapAlg f).hom (a + b) =
      (SymmetricAlgebra.lift ((bagι V).hom.comp f.hom)) a +
        (SymmetricAlgebra.lift ((bagι V).hom.comp f.hom)) b := by
  dsimp [symMapAlg]
  exact map_add (SymmetricAlgebra.lift ((bagι V).hom.comp f.hom)) a b

theorem symLiftAlg_map_mul {V : Vect k} {N : AddCommMon (Vect k)} (f : V ⟶ N.X)
    (a b : SymmetricAlgebra k V.carrier) :
    symLiftAlg f (a * b) = symLiftAlg f a * symLiftAlg f b := by
  dsimp [symLiftAlg]
  exact map_mul (SymmetricAlgebra.lift ((AlgHom.id k N.X.carrier).toLinearMap.comp f.hom)) a b

theorem symLiftAlg_map_add {V : Vect k} {N : AddCommMon (Vect k)} (f : V ⟶ N.X)
    (a b : SymmetricAlgebra k V.carrier) :
    symLiftAlg f (a + b) = symLiftAlg f a + symLiftAlg f b := by
  dsimp [symLiftAlg]
  exact map_add (SymmetricAlgebra.lift ((AlgHom.id k N.X.carrier).toLinearMap.comp f.hom)) a b

/-- The functorial action of symmetric algebra on linear maps. -/
noncomputable def symMap {V W : Vect k} (f : V ⟶ W) : symAddCommMon V ⟶ symAddCommMon W :=
  symMapAlg f

@[simp]
theorem symLift_hom {V : Vect k} {N : AddCommMon (Vect k)} (f : V ⟶ N.X) :
    (symLift f).hom = ModuleCat.ofHom (symLiftAlg f).toLinearMap := by
  dsimp [symLift, symLiftAlg]

@[simp]
theorem symMap_hom {V W : Vect k} (f : V ⟶ W) :
    (symMap f).hom =
      ModuleCat.ofHom
        (SymmetricAlgebra.lift ((bagι W).hom.comp f.hom)).toLinearMap := by
  dsimp [symMap, symMapAlg]

theorem symMapAlg_apply {U V W : Vect k} (f : U ⟶ V) (g : V ⟶ W)
    (x : SymmetricAlgebra k U.carrier) :
    (symMapAlg (f ≫ g)).hom x = (symMapAlg g).hom ((symMapAlg f).hom x) := by
  induction x using SymmetricAlgebra.induction with
  | algebraMap r =>
    dsimp [symMapAlg]
    simp only [AlgHom.commutes]
  | ι v =>
    calc (symMapAlg (f ≫ g)).hom (SymmetricAlgebra.ι k U.carrier v)
        _ = (bagι W).hom ((f ≫ g).hom v) := symMapAlg_ι (f ≫ g) v
        _ = (bagι W).hom (g.hom (f.hom v)) := by rw [comp_hom_apply]
        _ = (symMapAlg g).hom (SymmetricAlgebra.ι k V.carrier (f.hom v)) :=
            (symMapAlg_ι g (f.hom v)).symm
        _ = (symMapAlg g).hom ((symMapAlg f).hom (SymmetricAlgebra.ι k U.carrier v)) := by
            congr 1
            rw [symMapAlg_ι f v, bagι_apply]
  | mul a b ha hb =>
    rw [symMapAlg_hom_map_mul (f ≫ g) a b]
    conv_rhs => arg 2; rw [symMapAlg_hom_map_mul f a b]
    simp_rw [symMapAlg_hom_map_mul g _ _]
    simp only [symMapAlg_apply_lift] at ha hb ⊢
    rw [← ha, ← hb]
  | add a b ha hb =>
    rw [symMapAlg_hom_map_add (f ≫ g) a b]
    conv_rhs => arg 2; rw [symMapAlg_hom_map_add f a b]
    simp_rw [symMapAlg_hom_map_add g _ _]
    simp only [symMapAlg_apply_lift] at ha hb ⊢
    rw [← ha, ← hb]

@[simp]
theorem symMap_id (V : Vect k) : symMap (𝟙 V) = 𝟙 (symAddCommMon V) := by
  apply AddCommMon.hom_ext
  ext x
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => simp [symMap, symMapAlg, AlgHom.commutes]
  | ι v =>
    calc (symMap (𝟙 V)).hom (SymmetricAlgebra.ι k V.carrier v)
        _ = (bagι V).hom ((𝟙 V : V ⟶ V).hom v) := symMapAlg_ι (𝟙 V) v
        _ = SymmetricAlgebra.ι k V.carrier v := by rw [bagι_apply, ModuleCat.id_apply]
        _ = (AddMon.Hom.hom (𝟙 (symAddCommMon V))) (SymmetricAlgebra.ι k V.carrier v) := rfl
  | mul a b ha hb =>
    simp only [symMap] at ha hb ⊢
    rw [symMapAlg_hom_map_mul (𝟙 V) a b]
    simp only [symMapAlg_apply_lift] at ha hb ⊢
    rw [ha, hb]
    exact map_mul (AlgHom.id k (SymmetricAlgebra k V.carrier)) a b
  | add a b ha hb =>
    simp only [symMap] at ha hb ⊢
    rw [symMapAlg_hom_map_add (𝟙 V) a b]
    simp only [symMapAlg_apply_lift] at ha hb ⊢
    rw [ha, hb]
    exact map_add (AlgHom.id k (SymmetricAlgebra k V.carrier)) a b

@[simp]
theorem symMap_comp {U V W : Vect k} (f : U ⟶ V) (g : V ⟶ W) :
    symMap (f ≫ g) = symMap f ≫ symMap g := by
  apply AddCommMon.hom_ext
  ext x
  exact symMapAlg_apply f g x

noncomputable def bagFunctor : Vect k ⥤ AddCommMon (Vect k) where
  obj V := symAddCommMon V
  map f := symMap f
  map_id V := symMap_id V
  map_comp f g := symMap_comp f g

theorem symLift_apply {V : Vect k} {N : AddCommMon (Vect k)} (f : V ⟶ N.X)
    (x : SymmetricAlgebra k V.carrier) :
    (symLift f).hom x = symLiftAlg f x := by
  simp [symLift_hom]

theorem symMap_symLift_apply {U V : Vect k} {N : AddCommMon (Vect k)} (f : U ⟶ V) (g : V ⟶ N.X)
    (x : SymmetricAlgebra k U.carrier) :
    (symMap f ≫ symLift g).hom x = symLiftAlg g ((symMapAlg f).hom x) := by
  rw [AddCommMon.comp_hom, ModuleCat.comp_apply, symLift_apply, symMap, symMapAlg_apply_lift]

theorem symLift_bagι {V : Vect k} {N : AddCommMon (Vect k)} (f : symAddCommMon V ⟶ N) :
    symLift ((bagι V) ≫ f.hom) = f := by
  apply AddCommMon.hom_ext
  ext x
  induction x using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [symLift_apply, AlgHom.commutes]
    symm
    calc f.hom (algebraMap k (SymmetricAlgebra k V.carrier) r)
        _ = f.hom ((η[symObj V]).hom r) := by rw [η_symObj V, symZero_apply V r]
        _ = (η[symObj V] ≫ f.hom).hom r := (comp_hom_apply (η[symObj V]) f.hom r).symm
        _ = (η[N.X]).hom r := by rw [← f.isMonHom_hom.zero_hom]; rfl
        _ = (algebraMap k N.X.carrier) r := rfl
  | ι v =>
    rw [symLift_apply, symLiftAlg_ι, comp_hom_apply, bagι_apply V v]; rfl
  | mul a b ha hb =>
    simp only [symLift_apply] at ha hb ⊢
    rw [symLiftAlg_map_mul ((bagι V) ≫ f.hom) a b, ha, hb]
    rw [← addCommMonMul_eq_mul, ← addCommMonHom_map_mul f a b, symAddCommMon_mul]
  | add a b ha hb =>
    simp only [symLift_apply] at ha hb ⊢
    rw [symLiftAlg_map_add ((bagι V) ≫ f.hom) a b, ha, hb, map_add]

theorem symLift_comp {U V : Vect k} {N : AddCommMon (Vect k)} (f : U ⟶ V) (g : V ⟶ N.X) :
    symLift (f ≫ g) = symMap f ≫ symLift g := by
  apply AddCommMon.hom_ext
  ext x
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => simp [symLift_apply, symLiftAlg, symMapAlg, AlgHom.commutes]
  | ι v =>
    calc symLiftAlg (f ≫ g) (SymmetricAlgebra.ι k U.carrier v)
        _ = (f ≫ g).hom v := symLiftAlg_ι (f ≫ g) v
        _ = g.hom (f.hom v) := by rw [comp_hom_apply]
        _ = symLiftAlg g (SymmetricAlgebra.ι k V.carrier (f.hom v)) := (symLiftAlg_ι g (f.hom v)).symm
        _ = symLiftAlg g ((symMapAlg f).hom (SymmetricAlgebra.ι k U.carrier v)) := by
            congr 1
            rw [symMapAlg_ι f v, bagι_apply]
  | mul a b ha hb =>
    simp only [symLift_apply, symMap_symLift_apply] at ha hb ⊢
    rw [symLiftAlg_map_mul (f ≫ g) a b, ha, hb]
    rw [← symLiftAlg_map_mul g ((symMapAlg f).hom a) ((symMapAlg f).hom b)]
    rw [symMapAlg_hom_map_mul f a b, symMapAlg_apply_lift f a, symMapAlg_apply_lift f b]
  | add a b ha hb =>
    simp only [symLift_apply, symMap_symLift_apply] at ha hb ⊢
    rw [symLiftAlg_map_add (f ≫ g) a b, ha, hb]
    rw [← symLiftAlg_map_add g ((symMapAlg f).hom a) ((symMapAlg f).hom b)]
    rw [symMapAlg_hom_map_add f a b, symMapAlg_apply_lift f a, symMapAlg_apply_lift f b]

theorem bagι_symLift {V : Vect k} {N : AddCommMon (Vect k)} (f : V ⟶ N.X) :
    (bagι V) ≫ (symLift f).hom = f := by
  ext v
  rw [comp_hom_apply, bagι_apply V v, symLift_hom]
  exact symLiftAlg_ι f v

/-- Adjunction exhibiting `Sym(V)` as the free internal commutative monoid on `V`. -/
noncomputable def bagAdjunction : bagFunctor ⊣ AddCommMon.forget (Vect k) :=
  Adjunction.mkOfHomEquiv {
    homEquiv V M := {
      toFun f := (bagι V) ≫ f.hom
      invFun f := symLift f
      left_inv f := symLift_bagι f
      right_inv f := bagι_symLift f
    }
    homEquiv_naturality_left_symm := by
      intros U V M f g
      ext h
      simp only [Equiv.coe_fn_symm_mk, symLift_comp, bagFunctor, AddCommMon.comp_hom, comp_hom_apply]
    homEquiv_naturality_right V V' := by
      simp only [Equiv.coe_fn_mk, AddCommMon.comp_hom, comp_hom_apply]
      rfl
  }

noncomputable instance withBags : WithBags (Vect k) where
  functor := bagFunctor
  adj := bagAdjunction

theorem eq_sym (V : Vect k) : bag V = symObj V := rfl

#check bag (ModuleCat.of k (Fin 3 → k))
#check @CategoryTheory.bag.ofList (Vect k) inferInstance inferInstance inferInstance inferInstance
  (ModuleCat.of k (Fin 3 → k))

end Vect

end CategoryTheory
