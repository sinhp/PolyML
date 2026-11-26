/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import PolyML.Monoidal.NNO
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# `Vect k` as `ModuleCat k`

The draft monoidal instance in this file has been superseded by Mathlib's
`ModuleCat` monoidal structure. Use `PolyML.Monoidal.Vect` for list arithmetic.
-/

universe u

namespace CategoryTheory

/-- Bundled `k`-vector spaces: Mathlib's `ModuleCat`. -/
abbrev Vect (k : Type u) [Field k] := ModuleCat k

end CategoryTheory
