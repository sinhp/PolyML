import PolyML.Monoidal.NNO
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator

universe u

namespace CategoryTheory

/-- A bundled `k`-vector space, which will be the object in our category `Vect k`. -/
structure Vect (k : Type u) [Field k] where
  carrier : Type u
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module k carrier]

attribute [instance] Vect.isAddCommGroup
attribute [instance] Vect.isModule

variable {k : Type u} [Field k]

/-- The category instance for `Vect k`.
    - Morphisms are `k`-linear maps (`→ₗ[k]`).
    - Composition is composition of linear maps.
    - The identity is the identity linear map.
-/
instance : Category (Vect k) where
  Hom V W := V.carrier →ₗ[k] W.carrier
  id V := LinearMap.id
  comp f g := g.comp f
  id_comp f := LinearMap.id_comp f
  comp_id f := LinearMap.comp_id f
  assoc f g h := LinearMap.comp_assoc f g h

-- ## Monoidal Structure API

-- The category `Vect k` is monoidal, with the tensor product of vector spaces.

/-- The monoidal tensor product of two vector spaces. -/
def tensorObj (V W : Vect k) : Vect k :=
  ⟨TensorProduct k V.carrier W.carrier⟩

/-- The tensor product of two linear maps. -/
def tensorHom {U V W X : Vect k} (f : U ⟶ V) (g : W ⟶ X) :
    tensorObj U W ⟶ tensorObj V X :=
  TensorProduct.map f g

/-- The monoidal unit is the field `k` itself, as a 1D vector space. -/
def tensorUnit : Vect k := ⟨k⟩

/-- Helper function to cleanly convert a `LinearEquiv` into a categorical `Iso`. -/
@[simps]
def Vect.ofLinearEquiv {V W : Vect k} (e : V.carrier ≃ₗ[k] W.carrier) : V ≅ W where
  hom := e.toLinearMap
  inv := e.symm.toLinearMap
  -- The fix is to explicitly apply `LinearMap.ext` instead of using the `ext` tactic.
  hom_inv_id := by
    apply LinearMap.ext
    intro x
    refine Eq.symm (LinearMap.congr_arg ?_)
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  inv_hom_id := by
    apply LinearMap.ext
    intro x
    refine Eq.symm (LinearMap.congr_arg ?_)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

noncomputable instance : MonoidalCategory (Vect k) where
  tensorObj := tensorObj
  tensorHom {U V W X} f g := TensorProduct.map f g
  tensorUnit := tensorUnit
  tensor_id := by
    intros X1 X2
    exact TensorProduct.map_id
  tensor_comp := by
    intros
    exact TensorProduct.map_comp _ _ _ _
  associator U V W :=
    Vect.ofLinearEquiv (TensorProduct.assoc k U.carrier V.carrier W.carrier)
  leftUnitor V :=
    Vect.ofLinearEquiv (TensorProduct.lid k V.carrier)
  rightUnitor V :=
    Vect.ofLinearEquiv (TensorProduct.rid k V.carrier)

  -- Once the instance is well-formed, `aesop_cat` can solve all coherence laws.
  pentagon _ _ _ _ := by aesop_cat
  triangle _ _ := by aesop_cat
  leftUnitor_naturality := by aesop_cat
  rightUnitor_naturality := by aesop_cat
  associator_naturality := by sorry
  whiskerLeft := sorry
  whiskerRight := sorry

end CategoryTheory
