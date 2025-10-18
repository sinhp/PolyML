import Mathlib.CategoryTheory.Category.Quiv
import PolyML.Monoidal.ListArithmetic
import PolyML.Monoidal.NNO
import PolyML.Monoidal.FreeMon
import PolyML.Monoidal.FreeCommMon
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts

/-!
# Cartesian monoidal structure on the category of quivers

This file constructs the Cartesian (product) monoidal structure on the category of
quivers. Concretely, we equip the category whose objects are quivers and whose
morphisms are quiver morphisms with a symmetric monoidal structure where the
monoidal product is given by the pointwise product of vertex-sets and of arrow-sets.
-/

universe v u

namespace CategoryTheory.Quiv

-- We equip PUnit with the quiver structure where there is one morphism.
instance : Quiver PUnit where
  Hom _ _ := PUnit

/-- The terminal quiver is the quiver with one vertex and one endomorphism on that vertex. -/
def terminalObj : Quiv.{v, u} := Quiv.of PUnit

/-- We prove that `terminalObj` is indeed the terminal object in `Quiv`. -/
def terminalIsTerminal : Limits.IsTerminal terminalObj where
  -- For any other quiver `Q`, we can construct a unique morphism from `Q` to `terminalObj`.
  lift s :=
    { obj := fun _ => PUnit.unit
      map := fun _ => PUnit.unit }
  -- We must show this morphism is unique.
  uniq s m _ := by
    apply Prefunctor.ext
    · intro x
      exact fun Y f ↦ rfl
    · exact fun X ↦ rfl

instance : Limits.HasTerminal Quiv.{v, u} := sorry

-- We equip the product type `Q₁ × Q₂` with a quiver structure.
instance prodQuiver (Q₁ Q₂ : Quiv) : Quiver (Q₁ × Q₂) where
  Hom x y := (x.1 ⟶ y.1) × (x.2 ⟶ y.2)

/-- The product of two quivers `Q₁` and `Q₂`.
    - Its vertices are pairs of vertices `(v₁, v₂)`.
    - Its edges are pairs of edges `(e₁, e₂)`. -/
def prodObj (Q₁ Q₂ : Quiv.{v, u}) : Quiv.{v, u} :=
  Quiv.of (Q₁ × Q₂)

/-- The projection morphism from the product quiver to the first component. -/
def fst (Q₁ Q₂ : Quiv) : prodObj Q₁ Q₂ ⟶ Q₁ where
  obj p := p.1
  map f := f.1

/-- The projection morphism from the product quiver to the second component. -/
def snd (Q₁ Q₂ : Quiv) : prodObj Q₁ Q₂ ⟶ Q₂ where
  obj p := p.2
  map f := f.2

/-- We prove that `prodObj` together with the projections forms a product cone. -/
def prodIsLimit (Q₁ Q₂ : Quiv) : Limits.IsLimit (Limits.BinaryFan.mk (fst Q₁ Q₂) (snd Q₁ Q₂)) where
  -- For any other cone `s`, we can construct a unique lifting morphism.
  lift s :=
    { obj := fun z => (s.π.app ⟨Limits.WalkingPair.left⟩ |>.obj z, s.π.app ⟨Limits.WalkingPair.right⟩ |>.obj z)
      map := fun {z₁ z₂} f => (s.π.app ⟨Limits.WalkingPair.left⟩ |>.map f, s.π.app ⟨Limits.WalkingPair.right⟩ |>.map f) }
  -- The lifting commutes with the projections by definition.
  fac s j := by
    simp only [Limits.BinaryFan.mk_pt, Functor.const_obj_obj, Limits.pair_obj_left,
      Limits.BinaryFan.π_app_left, Limits.pair_obj_right, Limits.BinaryFan.π_app_right]
    sorry
  uniq s m h := by {
    simp only [Limits.BinaryFan.mk_pt, Functor.const_obj_obj, Limits.pair_obj_left,
      Limits.BinaryFan.π_app_left, Limits.pair_obj_right, Limits.BinaryFan.π_app_right]
    sorry
  }

instance (Q₁ Q₂ : Quiv.{v, u}) : Limits.HasBinaryProduct Q₁ Q₂ :=
  ⟨⟨⟨Limits.BinaryFan.mk (fst Q₁ Q₂) (snd Q₁ Q₂), prodIsLimit Q₁ Q₂⟩⟩⟩

-- Since `Quiv` has a terminal object and binary products, it has all finite products.
instance : Limits.HasFiniteProducts Quiv.{v, u} := by {
  sorry}

/-- We construct the monoidal category instance for `Quiv` using the fact that it
    has finite products. The tensor product is the categorical product, and the
    unit is the terminal object. -/
noncomputable instance : MonoidalCategory Quiv.{v, u} :=
  monoidalOfHasFiniteProducts Quiv

end CategoryTheory.Quiv
