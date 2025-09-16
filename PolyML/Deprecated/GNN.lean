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

def P : Matrix m m α := PEquiv.toMatrix (Equiv.toPEquiv σ)

def FunIsPermInvar (f : (Matrix m n α) → n → α) : Prop := f ((P σ) * X) = f X

example (ψ φ : (n → α) → n → α) : n → α := φ (∑ u ∈ (univ : Finset m), ψ (X u))

example : FunIsPermInvar X σ (Finset.sum univ) := by
  unfold FunIsPermInvar Finset.sum
  simp only [sum_map_val]
  nth_rw 2 [sum_perm σ]
  apply Finset.sum_congr
  simp only
  intros x hx
  ext i
  unfold P
  rw [PEquiv.toMatrix_mul_apply]
  simp only
  simp only [Equiv.toPEquiv_apply]

def FunIsPermInvar' (F : Matrix m n α → Matrix m n α) : Prop := F ((P σ) * X) = P σ * F (X)

variable (A : Matrix m m α) (hA : A.IsAdjMatrix)

def GraphWiseFunIsPermInvariant (f : (Matrix m n α) × (Matrix m m α) → R) : Prop :=
   f ((P σ * X), (P σ * A * (P σ).transpose)) = f (X, A)

def NodeWiseFunIsPermInvariant (F : (Matrix m n α) × (Matrix m m α) →  (Matrix m m α)) : Prop :=
  F ((P σ * X), (P σ * A * (P σ).transpose))  = (P σ) * F (X, A)

/-- Definition of permutation invariance for --to--categorified aggregator function -/
def FunIsPermInvarMultiset (f : Multiset R → R) : Prop :=
    ∀ (σ : Equiv.Perm R) (S : Multiset R), f (S.map (σ.toFun)) = f S

/-
If we're doing proofs, then Fin n → X is surely going to be best.
If we're programming, then Vector will be best.
If we're doing both, then we'll need to convert! #check Vector.ofFn
-/

variable {R U : Type*} (σ : Equiv.Perm U) (X : Matrix U (Fin k) R)

variable (G : Digraph U) [DecidableRel G.Adj] [Fintype U] [DecidableEq U]

/--the 1-hop neighborhood including the node itself-/
def N (u : U) : Finset U := {v | G.Adj v u ∨ G.Adj u v}.toFinset ∪ {u}

--variable [LinearOrderedField R]

def XN (u : U) [Fintype (Fin k → R)] : Multiset (Fin k → R) := (N G u).val.map (X ·)

def Digraph.pred (u : U) : Finset U := {v | G.Adj v u}.toFinset

variable [Semiring R]
--U:= Fin k
class GraphNeuralNetwork (R U : Type*) [DecidableEq U] [Fintype U]
   [Semiring R] (σ : Equiv.Perm U) extends Digraph U where
 (Uin Uout Uhidden : Finset U)
 (hU : Finset.univ = (Uin ∪ Uout ∪ Uhidden : Finset U))
 (hUin : Uin ≠ ∅)
 (hout : Uout ≠ ∅)
 (hhinout : Uhidden ∩ (Uin ∪ out) = ∅)
 (X : Matrix U U R)
 (w : ∀ u v : U, Adj u v → R)
 (ψ : ((U → R) × (U → R)) → (U → R))
 (aggregator : (Multiset (U → R)) → U → R)
 (hInv : FunIsPermInvarMultiset aggregator)
 (φ : ((U → R) × (U → R)) → (U → R))
 (h : ∀ u : U, U → R)

variable (GNN : GraphNeuralNetwork R U σ)
  [DecidableRel (GraphNeuralNetwork.toDigraph R σ).Adj]

def msg (u : U) : U → R :=
  fun i => GNN.aggregator (Multiset.map (fun v => GNN.ψ (GNN.X u, GNN.X v) i) (N G u).val)

def h (u : U) : U → R := GNN.φ (GNN.X u, msg σ GNN.toDigraph GNN u)

/-- An example of a message function where the aggregator is sum. -/
def message (u : U) : U → R := ∑ v in (N G u), (GNN.ψ (GNN.X u, GNN.X v))

/--An example of an update function with message function where the aggregator is sum -/
example (u : U) : U → R := GNN.φ (GNN.X u, message σ GNN.toDigraph GNN u)

variable {n m k : ℕ} {R : Type*} [Semiring R] (X : Matrix (Fin n) (Fin k) R)

def ψ : (Fin k → R) → (Fin k → R) → Fin m → R :=
   fun sender_vec receiver_vec i => if h : i.val < k then
               sender_vec ⟨i.val, h⟩ + receiver_vec ⟨i.val, h⟩
             else
               0

def φ : (Fin m → R) → Fin m → R := fun agg_msg i => agg_msg i + agg_msg i

-- Assume a Semiring R and dimensions n, m, k
variable {n m k : ℕ} {R : Type*} [Semiring R] [Fintype (Fin n)]

variable (X : Matrix (Fin n) (Fin k) R)

def pseudocode' : Matrix (Fin n) (Fin m) R := by
  -- ψ: (sender_vec + receiver_vec), padded with 0 if m > k.
  let ψ (sender_vec receiver_vec : Fin k → R) : Fin m → R :=
    fun i => if h : i.val < k then
               sender_vec ⟨i.val, h⟩ + receiver_vec ⟨i.val, h⟩
             else
               0
  -- φ: Double the aggregated message vector
  let φ (agg_msg : Fin m → R) : Fin m → R :=
    fun i => agg_msg i + agg_msg i

  -- Compute messages for all pairs of nodes (sender, receiver)
  -- This corresponds to: `for (u, v) ∈ V × V do msguv ← ψ(...)`
  let msgs : Matrix (Fin n) (Fin n) (Fin m → R) :=
    fun sender receiver => ψ (X sender) (X receiver)

  -- For each node `u`, aggregate incoming messages and update
  -- This corresponds to: `for u ∈ V do hu ← ϕ(⊕ v∈V msgvu)`
  let H : Matrix (Fin n) (Fin m) R :=
    fun u =>
      -- Aggregate all messages where `u` is the receiver
      -- We sum over all possible senders `v`
      let aggregatedMessage : Fin m → R :=
        ∑ v : Fin n, msgs v u

      -- b. Apply the update function `φ` to the aggregated message.
      φ aggregatedMessage

  -- 3. Provide the final matrix H as the result of the definition.
  exact H

instance {n m : ℕ} [Repr α] : Repr (Matrix (Fin n) (Fin m) α) where
  reprPrec m _ := repr (List.ofFn fun i => List.ofFn fun j => m i j)

-- Define concrete dimensions for our example
def N' : ℕ := 2  -- Number of nodes
def K : ℕ := 2  -- Input feature dimension
def M : ℕ := 3  -- Latent (message) feature dimension

-- Example node features X: a 2x2 matrix of natural numbers.
-- Node 0 has features [1, 2]
-- Node 1 has features [3, 4]
def X_example : Matrix (Fin N') (Fin K) ℕ :=
  fun i j => if i.val = 0 then j.val + 1 else j.val + 3

#eval pseudocode' (R := ℕ) (n := N') (m := M) (k := K) X_example
