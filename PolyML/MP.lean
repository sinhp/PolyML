/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import PolyML.FreeCommMon
import Mathlib.Algebra.Ring.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.FinEnum

import PolyML.BagInType


variable {E B : Type*} (p : E → B)

local notation "𝔼" => fun (b : B) => p ⁻¹' (Set.singleton b : Set B)

class FinEnumFibres where
  enum (b : B) : FinEnum (𝔼 b) := by infer_instance

instance [FinEnumFibres p] : ∀ b, FinEnum (𝔼 b) := fun b => FinEnumFibres.enum (p:=p) b

class HasFiniteFibres : Prop where
  finit_fibre : ∀ b : B, (𝔼 b).Finite

/-- Every map with finite fibres has finitely denumerable fibres.
SH: I'll refactor this for porting.
-/
noncomputable instance finEnumFibresOfHasFiniteFibres [HasFiniteFibres p] : FinEnumFibres p where
  enum b := by
    have := HasFiniteFibres.finit_fibre (p:= p) b
    apply finite_iff_exists_equiv_fin.mp at this
    choose n hn using this
    refine {
      card := n
      equiv := Classical.choice hn
      decEq := by simp; exact Classical.decEq (𝔼 b)
    }

def listOfFinEnumFibre (b : B) [FinEnum (𝔼 b)] : List (𝔼 b) :=
  FinEnum.toList _ -- SH: List.ofFn FinEnum.equiv.invFun also works.

/-- Converts a finite enumeration of elements in the fibres into a list of elements in the fibres. -/
def listOfFinEnumFibres [FinEnumFibres p] (b : B) : List (𝔼 b) :=
  listOfFinEnumFibre p b

def listOfFinEnumFibres' [FinEnumFibres p] : B → List (E) :=
  fun b => listOfFinEnumFibres p b |>.map Subtype.val

variable {I O : Type*}

structure PolyType where
  i : E → I
  o : B → O
  p : E → B
  [finEnumFibres : FinEnumFibres p]

namespace PolyType

variable (i : E → I) (o : B → O)

variable {R : Type*} [Semiring R]

def pullback (m : I → R) : E → R := m ∘ i

def aggregate : List R → R := List.foldr (fun x y => x * y) 1

def pushforward [FinEnumFibres p] (m : E → R) : B → R :=
  fun b => (listOfFinEnumFibres p b) |> List.map m |> aggregate

def pushdown [FinEnumFibres p] (m : B → R) : O → R :=
  fun e => m (p e)




end PolyType
