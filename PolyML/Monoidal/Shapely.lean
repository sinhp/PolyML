/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Functor.Category

/-!
# Pullback-Preserving Functors

This file defines pullback-preserving functors and develops a basic API for them.

A functor `F : C ⥤ D` is **pullback-preserving** if it maps pullback squares in `C` to
pullback squares in `D`.

## Main Definitions

* `PreservesPullbacks`: A functor preserves all pullbacks.
* `PreservesPullbacksOfSize`: A functor preserves pullbacks of a given universe size.

## Main Results

* `PreservesPullbacks.comp`: Composition of pullback-preserving functors preserves pullbacks.
* `PreservesPullbacks.id`: The identity functor preserves pullbacks.
* `PreservesPullbacks.ofIsPullback`: A functor preserves pullbacks iff it maps `IsPullback`
  squares to `IsPullback` squares.

## References

* [nLab, *pullback-preserving functor*](https://ncatlab.org/nlab/show/pullback-preserving+functor)
* Jay, C. Barry. "A semantics for shape." Science of computer programming 25.2-3 (1995): 251-283.

-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

#check HasPullback

#check PreservesLimit

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]



/-- A functor `F` preserves pullbacks if it maps pullback squares to pullback squares. -/
class PreservesPullbacks' (F : C ⥤ D) where
  /-- `F` preserves the pullback of any cospan. -/
  preserves : ∀ {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}, PreservesLimit (cospan f g) F

/-- A functor `F` preserves pullbacks if it maps pullback squares to pullback squares. -/
class PreservesPullbacks (F : C ⥤ D) : Prop where
  /-- `F` preserves the pullback of any cospan. -/
  preserves {W X Y Z : C} (fst : W ⟶ X) (snd : W ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
  (hc : IsPullback fst snd f g) : IsPullback (F.map fst) (F.map snd) (F.map f) (F.map g)

attribute [instance] PreservesPullbacks.preserves

namespace PreservesPullbacks

/-- The identity functor preserves pullbacks. -/
instance id : PreservesPullbacks (𝟭 C) where
  preserves := sorry

/-- Composition of pullback-preserving functors preserves pullbacks. -/
instance comp (F : C ⥤ D) [PreservesPullbacks F] (G : D ⥤ E) [PreservesPullbacks G] : PreservesPullbacks (F ⋙ G) where
  preserves := sorry

variable {X Y : C} (f : X ⟶ Y)

/-- A pullback-preserving functor preserves monomorphisms. -/
theorem map_mono (F : C ⥤ D) [PreservesPullbacks F]  [Mono f] [PreservesPullbacks F] :
    Mono (F.map f) := by
  constructor
  intro Z g h hfg
  -- Use the fact that mono is equivalent to the diagonal being an iso
  have : g ≫ F.map f = h ≫ F.map f := hfg
  sorry

-- If `F` and `G` are naturally isomorphic and `F` preserves pullbacks, then so does `G`. -/
theorem of_natIso (F : C ⥤ D) [PreservesPullbacks F]
    (G : C ⥤ D) [PreservesPullbacks G] (e : F ≅ G) :
    PreservesPullbacks G where
  preserves := fun {X Y Z f g} =>
    sorry

end PreservesPullbacks

end CategoryTheory
