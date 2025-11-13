import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fin.Fin2
import Mathlib.Data.Matrix.PEquiv

set_option linter.unusedVariables false

open Mathlib Finset

universe u v

variable {m n : Type*} {α : Type v} [Fintype m] [Semiring α]

variable (X : Matrix m n α) (σ : Equiv.Perm m)

lemma sum_perm (f : m → α) : ∑ x, f x = ∑ x, f (σ x) := Eq.symm (Equiv.sum_comp σ f)

variable  [DecidableEq m]

abbrev P : Matrix m m α := PEquiv.toMatrix (Equiv.toPEquiv σ)

def FunIsPermInvar (f : (Matrix m n α) → n → α) : Prop := f ((P σ) * X) = f X

example (ψ φ : (n → α) → n → α) : n → α := φ (∑ u ∈ (univ : Finset m), ψ (X u))

def sum_is_perm_invar (α : Type) : FunIsPermInvar X σ (Finset.sum univ) := by
  unfold FunIsPermInvar Finset.sum
  simp only [sum_map_val]
  nth_rw 2 [sum_perm σ]
  apply Finset.sum_congr rfl
  intros x hx
  ext i
  rw [PEquiv.toMatrix_mul_apply, Equiv.toPEquiv_apply]

def FunIsPermInvar' (F : Matrix m n α → Matrix m n α) : Prop := F ((P σ) * X) = P σ * F (X)

variable (A : Matrix m m α) (hA : A.IsAdjMatrix)

def GraphWiseFunIsPermInvariant (f : (Matrix m n α) × (Matrix m m α) → R) : Prop :=
   f ((P σ * X), (P σ * A * (P σ).transpose)) = f (X, A)

def NodeWiseFunIsPermInvariant (F : (Matrix m n α) × (Matrix m m α) →  (Matrix m m α)) : Prop :=
  F ((P σ * X), (P σ * A * (P σ).transpose)) = (P σ) * F (X, A)

/-- Definition of permutation invariance for --to--categorified aggregator function -/
def FunIsPermInvarMultiset (f : Multiset R → R) : Prop :=
  ∀ (σ : Equiv.Perm R) (S : Multiset R), f (S.map σ) = f S

/-- Proof that sum is permutation invariant -/
lemma sum_is_perm_invar_multiset [AddCommMonoid R] :
    FunIsPermInvarMultiset (Multiset.sum : Multiset R → R) := by
  sorry

variable {R U : Type*} (σ : Equiv.Perm U) (X : Matrix U (Fin k) R)

variable (G : Digraph U) [DecidableRel G.Adj] [Fintype U] [DecidableEq U]

/--the 1-hop neighborhood including the node itself-/
def Neigh (u : U) : Finset U := {v | G.Adj v u ∨ G.Adj u v}.toFinset ∪ {u}

def XN (u : U) [Fintype (Fin k → R)] : Multiset (Fin k → R) := (Neigh G u).val.map (X ·)

def Digraph.pred (u : U) : Finset U := {v | G.Adj v u}.toFinset

variable [Semiring R]

structure GraphNeuralNetwork (R U : Type*) (k : ℕ) [DecidableEq U] [Fintype U] [Semiring R]
  extends Digraph U where
 (ψ : (Fin k → R) → (Fin k → R) → (Fin k → R))
 (aggregator : (Multiset (Fin k → R)) → (Fin k → R))
 (φ : (Fin k → R) → (Fin k → R) → (Fin k → R))
 (hInv : FunIsPermInvarMultiset aggregator)
 (h : ∀ u : U, U → R)

structure GraphNeuralNetwork.Params (U : Type*) (k : ℕ) where
  (X : Matrix U (Fin k) R)

variable {U : Type*} (k : ℕ) [Fintype U] (σ : Equiv.Perm U) [DecidableEq U] (GNN : GraphNeuralNetwork R U k)
  (params : GraphNeuralNetwork.Params U k) [DecidableRel (GNN.toDigraph).Adj]

-- MESSAGE - Compute an incoming message from EACH neighbor `v`.
-- The result is a collection (a Multiset) of message vectors.
def incoming_messages (u : U) : Multiset (Fin k → R) :=
  (Neigh GNN.toDigraph u).val.map (fun v => GNN.ψ (params.X u) (params.X v))
-- Message from `v` to `u`

-- AGGREGATE - Combine the collection of messages into a single vector.
def aggregated_message (u : U) : Fin k → R :=
  GNN.aggregator (incoming_messages k GNN params u)

-- UPDATE - Use the node's original features and the aggregated message
-- to compute the new feature vector for `u`.
def new_features_for_u (u : U) : Fin k → R :=
  GNN.φ (params.X u) (aggregated_message k GNN params u)
