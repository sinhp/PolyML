/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import PolyML.Monoidal.WithPListListArithmetic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# List arithmetic in `k`-vector spaces (`ModuleCat k`)

Mathlib already provides the monoidal category of `R`-modules (`ModuleCat R`); for a field `k`
this is the usual category **`Vect k`** of vector spaces with tensor product.

We construct a parameterized list object on each object `V` as the direct sum of tensor powers
`⨁_{n : ℕ} V^{⊗ n}`, then obtain `[ListArithmetic (ModuleCat k)]`.
-/

universe u

namespace CategoryTheory

open MonoidalCategory ModuleCat DirectSum

open scoped TensorProduct

/-- The category of `k`-vector spaces, bundled as Mathlib's `ModuleCat`. -/
abbrev Vect (k : Type u) [Field k] := ModuleCat k

namespace Vect

variable {k : Type u} [Field k]

/-- `n`-fold tensor power of a vector space in `Vect k`. -/
noncomputable def tensorPower (V : Vect k) : ℕ → Vect k
  | 0 => ModuleCat.of k k
  | n + 1 => V ⊗ tensorPower V n

/-- The carrier of the `n`-th tensor power. -/
@[reducible]
def listFamily (V : Vect k) (n : ℕ) : Type u := (tensorPower V n).carrier

noncomputable instance listFamilyAddCommMonoid (V : Vect k) (n : ℕ) : AddCommMonoid (listFamily V n) := by
  dsimp [listFamily]
  infer_instance

noncomputable instance listFamilyModule (V : Vect k) (n : ℕ) : Module k (listFamily V n) := by
  dsimp [listFamily]
  infer_instance

@[simp]
theorem listFamily_zero (V : Vect k) : listFamily V 0 = k := rfl

@[simp]
theorem listFamily_succ (V : Vect k) (n : ℕ) :
    listFamily V (n + 1) = (V ⊗ tensorPower V n).carrier := rfl

/-- The list object on `V`: `L V = ⨁_{n : ℕ} V^{⊗ n}`. -/
noncomputable def listObj (V : Vect k) : Vect k :=
  ModuleCat.of k (⨁ (n : ℕ), listFamily V n)

/-- Embed `a ⊗ x` into degree `n + 1` of the direct sum. -/
noncomputable def shiftComponent (V : Vect k) (a : V.carrier) (n : ℕ) :
    listFamily V n →ₗ[k] ⨁ m, listFamily V m :=
  (DirectSum.lof k ℕ (listFamily V) (n + 1)).comp
    (TensorProduct.mk k V.carrier (listFamily V n) a)

theorem shiftComponent_add (V : Vect k) (a₁ a₂ : V.carrier) (n : ℕ) :
    shiftComponent V (a₁ + a₂) n = shiftComponent V a₁ n + shiftComponent V a₂ n := by
  simp only [shiftComponent]
  rw [show (TensorProduct.mk k V.carrier (listFamily V n) (a₁ + a₂)) =
      TensorProduct.mk k V.carrier (listFamily V n) a₁ +
        TensorProduct.mk k V.carrier (listFamily V n) a₂ by
    ext x; simp [TensorProduct.add_tmul, TensorProduct.mk_apply]]
  simp [LinearMap.comp_add, map_add]

theorem shiftComponent_smul (V : Vect k) (c : k) (a : V.carrier) (n : ℕ) :
    shiftComponent V (c • a) n = c • shiftComponent V a n := by
  simp only [shiftComponent]
  rw [show (TensorProduct.mk k V.carrier (listFamily V n) (c • a)) =
      c • TensorProduct.mk k V.carrier (listFamily V n) a by
    ext x; simp [TensorProduct.tmul_smul, TensorProduct.mk_apply]]
  simp [LinearMap.comp_smul, map_smul]

theorem shiftComponent_family_add (V : Vect k) (a₁ a₂ : V.carrier) :
    shiftComponent V (a₁ + a₂) = shiftComponent V a₁ + shiftComponent V a₂ := by
  funext n
  exact shiftComponent_add V a₁ a₂ n

theorem shiftComponent_family_smul (V : Vect k) (c : k) (a : V.carrier) :
    shiftComponent V (c • a) = c • shiftComponent V a := by
  funext n
  exact shiftComponent_smul V c a n

theorem toModule_family_add (V : Vect k) (φ ψ : ∀ n, listFamily V n →ₗ[k] ⨁ m, listFamily V m)
    (d : ⨁ n, listFamily V n) :
    DirectSum.toModule k ℕ (⨁ m, listFamily V m) (φ + ψ) d =
      DirectSum.toModule k ℕ (⨁ m, listFamily V m) φ d +
        DirectSum.toModule k ℕ (⨁ m, listFamily V m) ψ d := by
  refine DirectSum.induction_on d (by simp) (fun n x => ?_) (fun x y hx hy => ?_)
  · rw [← DirectSum.lof_eq_of (R := k) (i := n) (b := x), DirectSum.toModule_lof,
      DirectSum.toModule_lof, DirectSum.toModule_lof, Pi.add_apply, LinearMap.add_apply]
  · rw [map_add (DirectSum.toModule k ℕ (⨁ m, listFamily V m) (φ + ψ)), hx, hy,
      map_add (DirectSum.toModule k ℕ (⨁ m, listFamily V m) φ),
      map_add (DirectSum.toModule k ℕ (⨁ m, listFamily V m) ψ)]
    abel

theorem toModule_family_smul (V : Vect k) (c : k) (φ : ∀ n, listFamily V n →ₗ[k] ⨁ m, listFamily V m)
    (d : ⨁ n, listFamily V n) :
    DirectSum.toModule k ℕ (⨁ m, listFamily V m) (c • φ) d =
      c • DirectSum.toModule k ℕ (⨁ m, listFamily V m) φ d := by
  refine DirectSum.induction_on d (by simp) (fun n x => ?_) (fun x y hx hy => ?_)
  · rw [← DirectSum.lof_eq_of (R := k) (i := n) (b := x), DirectSum.toModule_lof,
      DirectSum.toModule_lof, Pi.smul_apply, LinearMap.smul_apply]
  · rw [map_add (DirectSum.toModule k ℕ (⨁ m, listFamily V m) (c • φ)), hx, hy,
      ← smul_add c _ _, map_add (DirectSum.toModule k ℕ (⨁ m, listFamily V m) φ)]

/-- Prepend a vector from `V`, shifting the grading by one. -/
noncomputable def listConsLin (V : Vect k) :
    V.carrier ⊗[k] (⨁ n, listFamily V n) →ₗ[k] ⨁ n, listFamily V n :=
  TensorProduct.lift <|
    LinearMap.mk₂ k
      (fun a d => DirectSum.toModule k ℕ (⨁ m, listFamily V m) (shiftComponent V a) d)
      (by
        intro a₁ a₂ d
        change toModule k ℕ (⨁ m, listFamily V m) (shiftComponent V (a₁ + a₂)) d =
          toModule k ℕ (⨁ m, listFamily V m) (shiftComponent V a₁) d +
            toModule k ℕ (⨁ m, listFamily V m) (shiftComponent V a₂) d
        rw [shiftComponent_family_add V a₁ a₂]
        exact toModule_family_add V _ _ d)
      (by
        intro c a d
        change toModule k ℕ (⨁ m, listFamily V m) (shiftComponent V (c • a)) d =
          c • toModule k ℕ (⨁ m, listFamily V m) (shiftComponent V a) d
        rw [shiftComponent_family_smul V c a]
        exact toModule_family_smul V c _ d)
      (by
        intro a d₁ d₂
        simp [map_add, DirectSum.toModule_lof, shiftComponent, TensorProduct.mk_apply])
      (by
        intro a c d
        simp [map_smul, DirectSum.toModule_lof, shiftComponent, TensorProduct.mk_apply])

noncomputable def listCons (V : Vect k) : V ⊗ listObj V ⟶ listObj V :=
  ofHom (listConsLin V)

/-- The empty list, sitting in degree `0`. -/
noncomputable def listNil (V : Vect k) : 𝟙_ (Vect k) ⟶ listObj V :=
  ofHom <| DirectSum.lof k ℕ (listFamily V) (0 : ℕ)

section listPrc

variable {V : Vect k} {P B : Vect k}

open ModuleCat.MonoidalCategory

/-- Degree-wise parameterized list recursion. -/
noncomputable def listPrcStep (f : P ⟶ B) (g : V ⊗ B ⟶ B) :
    ∀ n, TensorProduct k (listFamily V n) P.carrier →ₗ[k] B.carrier
  | 0 =>
      f.hom.comp (TensorProduct.lid k P.carrier).toLinearMap
  | n + 1 =>
    (g.hom.comp (LinearMap.lTensor V.carrier (listPrcStep f g n))).comp
      (TensorProduct.assoc k V.carrier (listFamily V n) P.carrier).toLinearMap

/-- Parameterized list recursion on `listObj V`. -/
noncomputable def listPrc (f : P ⟶ B) (g : V ⊗ B ⟶ B) : listObj V ⊗ P ⟶ B :=
  ofHom <|
    DirectSum.toModule k ℕ B.carrier (listPrcStep f g) ∘ₗ
      (TensorProduct.directSumLeft k (listFamily V) P.carrier).toLinearMap

theorem listConsLin_tmul (V : Vect k) (v : V.carrier) (d : ⨁ n, listFamily V n) :
    listConsLin V (v ⊗ₜ[k] d) =
      DirectSum.toModule k ℕ (⨁ m, listFamily V m) (shiftComponent V v) d := by
  simp [listConsLin]

theorem listConsLin_tmul_lof (V : Vect k) (v : V.carrier) (n : ℕ) (x : listFamily V n) :
    listConsLin V (v ⊗ₜ[k] DirectSum.lof k ℕ (listFamily V) n x) =
      DirectSum.lof k ℕ (listFamily V) (n + 1) (v ⊗ₜ[k] x) := by
  rw [listConsLin_tmul, DirectSum.toModule_lof, shiftComponent, LinearMap.comp_apply]
  rfl

theorem listPrc_apply (f : P ⟶ B) (g : V ⊗ B ⟶ B) (d : ⨁ n, listFamily V n) (p : P.carrier) :
    (listPrc f g).hom (d ⊗ₜ[k] p) =
      DirectSum.toModule k ℕ B.carrier (listPrcStep f g)
        (TensorProduct.directSumLeft k (listFamily V) P.carrier (d ⊗ₜ[k] p)) := rfl

theorem listPrc_lof (f : P ⟶ B) (g : V ⊗ B ⟶ B) (n : ℕ) (x : listFamily V n) (p : P.carrier) :
    (listPrc f g).hom ((DirectSum.lof k ℕ (listFamily V) n x) ⊗ₜ[k] p) =
      listPrcStep f g n (x ⊗ₜ[k] p) := by
  rw [listPrc_apply, TensorProduct.directSumLeft_tmul_lof, DirectSum.toModule_lof]

theorem listPrcStep_zero_apply (f : P ⟶ B) (g : V ⊗ B ⟶ B) (r : k) (p : P.carrier) :
    listPrcStep f g 0 (r ⊗ₜ[k] p) = r • f.hom p := by
  simp [listPrcStep, LinearMap.comp_apply, TensorProduct.lid_tmul]

/-- `lof n x ⊗ p` with correct parenthesization. -/
noncomputable def listLofTmul (V : Vect k) (P : Vect k) (n : ℕ) (x : listFamily V n) (p : P.carrier) :
    (listObj V ⊗ P).carrier :=
  (DirectSum.lof k ℕ (listFamily V) n x) ⊗ₜ[k] p

/-- `v ⊗ lof n x`, parenthesized as an element of `V ⊗ listObj`. -/
noncomputable def listVinLof (V : Vect k) (v : V.carrier) (n : ℕ) (x : listFamily V n) :
    V.carrier ⊗[k] (listObj V) :=
  v ⊗ₜ[k] DirectSum.lof k ℕ (listFamily V) n x

/-- `(v ⊗ lof n x) ⊗ p` with correct parenthesization. -/
noncomputable def listConsOnVin (V : Vect k) (P : Vect k) (v : V.carrier) (n : ℕ)
    (x : listFamily V n) (p : P.carrier) : ((V ⊗ listObj V) ⊗ P).carrier :=
  (show V.carrier ⊗[k] (listObj V) from listVinLof V v n x) ⊗ₜ[k] p

theorem listConsLin_vin (V : Vect k) (v : V.carrier) (n : ℕ) (x : listFamily V n) :
    listConsLin V (listVinLof V v n x) =
      DirectSum.lof k ℕ (listFamily V) (n + 1) (v ⊗ₜ[k] x) := by
  dsimp [listVinLof]
  exact listConsLin_tmul_lof V v n x

theorem listConsRTensor (V : Vect k) (P : Vect k) (v : V.carrier) (n : ℕ)
    (x : listFamily V n) (p : P.carrier) :
    LinearMap.rTensor P (listConsLin V) (listConsOnVin V P v n x p) =
      listLofTmul V P (n + 1) (v ⊗ₜ[k] x) p := by
  dsimp [listConsOnVin]
  rw [listConsLin_vin, listLofTmul]

theorem listConsTmul_eq_lof (V : Vect k) (P : Vect k) (v : V.carrier) (n : ℕ)
    (x : listFamily V n) (p : P.carrier) :
    (listCons V ▷ P).hom (listConsOnVin V P v n x p) =
      listLofTmul V P (n + 1) (v ⊗ₜ[k] x) p := by
  rw [ModuleCat.hom_whiskerRight, listCons]
  exact listConsRTensor V P v n x p

theorem associator_listLofTmul (V : Vect k) (P : Vect k) (v : V.carrier) (n : ℕ)
    (x : listFamily V n) (p : P.carrier) :
    ((α_ V (listObj V) P).inv).hom (v ⊗ₜ[k] listLofTmul V P n x p) =
      listConsOnVin V P v n x p := by
  simp [associator_inv_apply, listLofTmul, listVinLof, listConsOnVin]

theorem listPrcStep_succ_apply (f : P ⟶ B) (g : V ⊗ B ⟶ B) (n : ℕ)
    (v : V.carrier) (x : listFamily V n) (p : P.carrier) :
    listPrcStep f g (n + 1) (v ⊗ₜ[k] x ⊗ₜ[k] p) =
      g.hom (v ⊗ₜ[k] listPrcStep f g n (x ⊗ₜ[k] p)) := by
  simp only [listPrcStep, LinearMap.comp_apply, LinearMap.lTensor_tmul]
  congr 1

theorem listConsLin_tmul_add (V : Vect k) (v : V.carrier) (d₁ d₂ : ⨁ n, listFamily V n) :
    listConsLin V (v ⊗ₜ[k] (d₁ + d₂)) =
      listConsLin V (v ⊗ₜ[k] d₁) + listConsLin V (v ⊗ₜ[k] d₂) := by
  rw [TensorProduct.tmul_add, map_add (listConsLin V)]

theorem listPrc_add (f : P ⟶ B) (g : V ⊗ B ⟶ B) (d₁ d₂ : ⨁ n, listFamily V n) (p : P.carrier) :
    (listPrc f g).hom ((d₁ + d₂) ⊗ₜ[k] p) =
      (listPrc f g).hom (d₁ ⊗ₜ[k] p) + (listPrc f g).hom (d₂ ⊗ₜ[k] p) := by
  rw [TensorProduct.add_tmul, map_add (listPrc f g).hom, listPrc_apply, listPrc_apply]

theorem listPrc_lof' (f : P ⟶ B) (g : V ⊗ B ⟶ B) (n : ℕ) (x : listFamily V n) (p : P.carrier) :
    (listPrc f g).hom (listLofTmul V P n x p) = listPrcStep f g n (x ⊗ₜ[k] p) := by
  dsimp [listLofTmul]
  exact listPrc_lof f g n x p

theorem lof_zero_smul (V : Vect k) (a : k) :
    (DirectSum.lof k ℕ V.listFamily 0) a =
      SMul.smul a ((DirectSum.lof k ℕ V.listFamily 0) (1 : k)) := by
  nth_rw 1 [← mul_one a]
  rw [show a * 1 = a • (1 : k) from by rw [smul_eq_mul, mul_one],
    map_smul (DirectSum.lof k ℕ V.listFamily 0)]
  change a • ((DirectSum.lof k ℕ V.listFamily 0) (1 : k)) =
      SMul.smul a ((DirectSum.lof k ℕ V.listFamily 0) (1 : k))
  rfl

theorem listLofTmul_zero_smul (V : Vect k) (P : Vect k) (a : k) (p : P.carrier) :
    listLofTmul V P 0 a p = SMul.smul a (listLofTmul V P 0 (1 : k) p) := by
  calc
    listLofTmul V P 0 a p = (DirectSum.lof k ℕ V.listFamily 0 a) ⊗ₜ[k] p := rfl
    _ = (SMul.smul a ((DirectSum.lof k ℕ V.listFamily 0) (1 : k))) ⊗ₜ[k] p := by
      rw [lof_zero_smul V a]
    _ = SMul.smul a (listLofTmul V P 0 (1 : k) p) := by
      change (a • ((DirectSum.lof k ℕ V.listFamily 0) (1 : k))) ⊗ₜ[k] p =
          a • listLofTmul V P 0 (1 : k) p
      dsimp [listLofTmul]
      rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]

theorem listLofTmul_add (V : Vect k) (P : Vect k) (n : ℕ) (x₁ x₂ : listFamily V n) (p : P.carrier) :
    listLofTmul V P n (x₁ + x₂) p = listLofTmul V P n x₁ p + listLofTmul V P n x₂ p := by
  dsimp [listLofTmul]
  rw [map_add (DirectSum.lof k ℕ (listFamily V) n), TensorProduct.add_tmul]

theorem listCons_listPrc_lof (V : Vect k) {P B : Vect k} {f : P ⟶ B} {g : V ⊗ B ⟶ B}
    (v : V.carrier) (n : ℕ) (x : listFamily V n) (p : P.carrier) :
    (listPrc f g).hom ((listCons V ▷ P).hom (listConsOnVin V P v n x p)) =
      g.hom (v ⊗ₜ[k] listPrcStep f g n (x ⊗ₜ[k] p)) := by
  rw [listConsTmul_eq_lof, listPrc_lof', listPrcStep_succ_apply]

theorem cons_prc_at_lof (V : Vect k) {P B : Vect k} {f : P ⟶ B} {g : V ⊗ B ⟶ B}
    (v : V.carrier) (n : ℕ) (x : listFamily V n) (p : P.carrier) :
    ((α_ V (listObj V) P).inv ≫ (listCons V ▷ P) ≫ listPrc f g).hom
      (v ⊗ₜ[k] listLofTmul V P n x p) =
    ((V ◁ listPrc f g) ≫ g).hom (v ⊗ₜ[k] listLofTmul V P n x p) := by
  have key := listCons_listPrc_lof (V := V) (P := P) (B := B) (f := f) (g := g) v n x p
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_comp]
  simp only [LinearMap.comp_apply, associator_listLofTmul, key]
  change (Hom.hom g) (v ⊗ₜ[k] listPrcStep f g n (x ⊗ₜ[k] p)) =
      (Hom.hom g) (LinearMap.lTensor V.carrier (listPrc f g).hom (v ⊗ₜ[k] listLofTmul V P n x p))
  congr 1
  rw [LinearMap.lTensor_tmul, listPrc_lof' f g n x p]

theorem prc_uniq_at_lof (V : Vect k) {P B : Vect k} {f : P ⟶ B} {g : V ⊗ B ⟶ B}
    {r : listObj V ⊗ P ⟶ B}
    (h_nil : (listNil V ▷ P) ≫ r = (λ_ P).hom ≫ f)
    (h_cons :
      (α_ V (listObj V) P).inv ≫ (listCons V ▷ P) ≫ r = (V ◁ r) ≫ g)
    (n : ℕ) (x : listFamily V n) (p : P.carrier) :
    r.hom (listLofTmul V P n x p) = (listPrc f g).hom (listLofTmul V P n x p) := by
  cases n with
  | zero =>
    have h1 : r.hom (listLofTmul V P 0 (1 : k) p) = f.hom p := by
      have := congrArg (fun φ => φ.hom ((1 : k) ⊗ₜ[k] p)) h_nil
      simp [listNil, whiskerRight_apply, leftUnitor_hom_apply, ModuleCat.hom_comp,
        LinearMap.comp_apply, listLofTmul, DirectSum.toModule_lof] at this
      exact this
    suffices ∀ (a : k), r.hom (listLofTmul V P 0 a p) = a • f.hom p by
      rw [this x, listPrc_lof', listPrcStep_zero_apply]
    intro a
    rw [listLofTmul_zero_smul V P a p]
    change (Hom.hom r) (a • listLofTmul V P 0 (1 : k) p) = a • (Hom.hom f) p
    rw [map_smul r.hom, h1]
  | succ n =>
    refine TensorProduct.induction_on x (by simp [listLofTmul, map_zero]) (fun v y => ?_) (fun x₁ x₂ hx₁ hx₂ => ?_)
    · have ih := prc_uniq_at_lof V h_nil h_cons n y p
      have hr : r.hom (listLofTmul V P (n + 1) (v ⊗ₜ[k] y) p) =
          ((α_ V (listObj V) P).inv ≫ (listCons V ▷ P) ≫ r).hom
            (v ⊗ₜ[k] listLofTmul V P n y p) := by
        rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
        simp only [LinearMap.comp_apply, associator_listLofTmul, listConsTmul_eq_lof]
      have ht := congrArg (fun φ => φ.hom (v ⊗ₜ[k] listLofTmul V P n y p)) h_cons
      have hlp : (listPrc f g).hom (listLofTmul V P (n + 1) (v ⊗ₜ[k] y) p) =
          g.hom (v ⊗ₜ[k] listPrcStep f g n (y ⊗ₜ[k] p)) := by
        rw [listPrc_lof', listPrcStep_succ_apply]
      have hchain : ((V ◁ r) ≫ g).hom (v ⊗ₜ[k] listLofTmul V P n y p) =
          (listPrc f g).hom (listLofTmul V P (n + 1) (v ⊗ₜ[k] y) p) := by
        have ih' := congrArg (fun t => v ⊗ₜ[k] t) ih
        have hl : LinearMap.lTensor V.carrier r.hom (v ⊗ₜ[k] listLofTmul V P n y p) =
            v ⊗ₜ[k] r.hom (listLofTmul V P n y p) :=
          LinearMap.lTensor_tmul V.carrier r.hom v (listLofTmul V P n y p)
        rw [ModuleCat.hom_comp, ModuleCat.hom_whiskerLeft, LinearMap.comp_apply]
        exact (congrArg g.hom hl.symm).trans <|
          (congrArg g.hom ih').trans <|
            (congrArg (fun t => g.hom (v ⊗ₜ[k] t)) (listPrc_lof' f g n y p)).trans hlp.symm
      exact hr.trans (ht.trans hchain)
    · rw [listLofTmul_add V P (n + 1) x₁ x₂ p, map_add r.hom, map_add (listPrc f g).hom, hx₁, hx₂]

end listPrc

section proofs

variable {V : Vect k} {P B : Vect k} {f : P ⟶ B} {g : V ⊗ B ⟶ B}

open ModuleCat.MonoidalCategory in
theorem nil_prc_proof :
    (listNil V ▷ P) ≫ listPrc f g = (λ_ P).hom ≫ f := by
  apply tensor_ext
  intro r p
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_hom_apply,
    map_smul, whiskerRight_apply, ModuleCat.hom_whiskerRight, listNil, listPrc, ModuleCat.hom_ofHom]
  change (DirectSum.toModule k ℕ B.carrier (listPrcStep f g))
      ((TensorProduct.directSumLeft k (listFamily V) P.carrier)
        (DirectSum.lof k ℕ (listFamily V) 0 r ⊗ₜ[k] p)) = r • f.hom p
  rw [TensorProduct.directSumLeft_tmul_lof, DirectSum.toModule_lof, listPrcStep,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  show f (r • p) = r • f p
  exact map_smul f.hom r p

open ModuleCat.MonoidalCategory in
theorem cons_prc_proof :
    (α_ V (listObj V) P).inv ≫ (listCons V ▷ P) ≫ listPrc f g =
      (V ◁ listPrc f g) ≫ g := by
  apply tensor_ext₃
  intro v d p
  refine DirectSum.induction_on d (by simp) (fun n x => cons_prc_at_lof V v n x p) (fun d₁ d₂ hd₁ hd₂ => by
    change ((α_ V (listObj V) P).inv ≫ (listCons V ▷ P) ≫ listPrc f g).hom
        (v ⊗ₜ[k] ((d₁ + d₂) ⊗ₜ[k] p)) =
      ((V ◁ listPrc f g) ≫ g).hom (v ⊗ₜ[k] ((d₁ + d₂) ⊗ₜ[k] p))
    rw [TensorProduct.add_tmul, TensorProduct.tmul_add]
    rw [map_add ((α_ V (listObj V) P).inv ≫ (listCons V ▷ P) ≫ listPrc f g).hom, hd₁, hd₂]
    rw [show ((V ◁ listPrc f g) ≫ g).hom (v ⊗ₜ[k] (d₁ ⊗ₜ[k] p) + v ⊗ₜ[k] (d₂ ⊗ₜ[k] p)) =
        ((V ◁ listPrc f g) ≫ g).hom (v ⊗ₜ[k] (d₁ ⊗ₜ[k] p)) +
          ((V ◁ listPrc f g) ≫ g).hom (v ⊗ₜ[k] (d₂ ⊗ₜ[k] p)) from
      map_add ((V ◁ listPrc f g) ≫ g).hom _ _])

open ModuleCat.MonoidalCategory in
theorem prc_uniq_proof {r : listObj V ⊗ P ⟶ B}
    (h_nil : (listNil V ▷ P) ≫ r = (λ_ P).hom ≫ f)
    (h_cons :
      (α_ V (listObj V) P).inv ≫ (listCons V ▷ P) ≫ r = (V ◁ r) ≫ g) :
    r = listPrc f g := by
  apply tensor_ext
  intro d p
  refine DirectSum.induction_on d (by simp) (fun n x => prc_uniq_at_lof V h_nil h_cons n x p)
    (fun d₁ d₂ hd₁ hd₂ => by
      rw [TensorProduct.add_tmul, map_add r.hom, map_add (listPrc f g).hom, hd₁, hd₂,
        (listPrc_add f g d₁ d₂ p).symm])

end proofs

@[simps!]
noncomputable def pList (V : Vect k) : PList V where
  L := listObj V
  nil := listNil V
  cons := listCons V
  isPList := {
    prc := listPrc
    nil_prc := nil_prc_proof
    cons_prc := cons_prc_proof
    prc_uniq := fun {P B f g r h_nil h_cons} => prc_uniq_proof h_nil h_cons
  }

noncomputable def withPList : WithPList (Vect k) := fun V => pList V

attribute [local instance] withPList

noncomputable example : ListArithmetic (Vect k) := inferInstance

#check ListArithmetic (Vect k)

/-- `Vect k` carries list arithmetic. -/
noncomputable example (k : Type u) [Field k] : ListArithmetic (Vect k) :=
  inferInstance

end Vect

end CategoryTheory
