-- import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Fin2

set_option linter.unusedVariables false

open Mathlib Finset

universe u v

@[ext]
structure Digraph (V : Type*) where
  Adj : V → V → Prop

variable {m n : Type*} {α : Type v} [Fintype m] [Semiring α]

variable (X : Matrix m n α) (σ : Equiv.Perm m)

lemma sum_perm (f : m → α) : ∑ x, f x = ∑ x, f (σ x) := Eq.symm (Equiv.sum_comp σ f)

variable  [DecidableEq m]

def P : Matrix m m α := PEquiv.toMatrix (Equiv.toPEquiv σ)

def FunIsPermInvar (f : (Matrix m n α) → n → α) : Prop := f ((P σ) * X) = f X

example (ψ φ : (n → α) → n → α) : n → α := φ (∑ u in (univ : Finset m), ψ (X u))

example : FunIsPermInvar X σ (Finset.sum univ) := by
  unfold FunIsPermInvar Finset.sum
  simp only [sum_map_val]
  nth_rw 2 [sum_perm σ]
  apply Finset.sum_congr
  simp only
  intros x hx
  ext i
  unfold P
  rw [PEquiv.mul_matrix_apply]
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

variable [LinearOrderedField R]

def XN (u : U) [Fintype (Fin k → R)] : Multiset (Fin k → R) := {X v | v ∈ N G u}.toFinset.val

def Digraph.pred (u : U) : Finset U := {v | G.Adj v u}.toFinset

class GraphNeuralNetwork (R U : Type*) [DecidableEq U] [Fintype U]
   [Semiring R] (σ : Equiv.Perm U) extends Digraph U where
 (Uin Uout Uhidden : Finset U)
 (hU : Finset.univ = (Uin ∪ Uout ∪ Uhidden : Finset U))
 (hUin : Uin ≠ ∅)
 (hout : Uout ≠ ∅)
 (hhinout : Uhidden ∩ (Uin ∪ out) = ∅)
 {k : ℕ}
 (X : Matrix U (Fin k) R)
 (w : ∀ u v : U, Adj u v → R)
 (ψ : ((Fin k → R) × (Fin k → R)) → (Fin k → R))
 (oplus : Multiset R → R)
 (hInv : FunIsPermInvarMultiset oplus)
 (φ : ((Fin k → R) × (Fin k → R)) → (Fin k → R))
 (h : ∀ u : U, Fin k → R)

variable (GNN : GraphNeuralNetwork R U σ) [DecidableRel (GraphNeuralNetwork.toDigraph R σ).Adj]

def msg (u : U) : Fin (GraphNeuralNetwork.k R σ) → R :=
  fun i => GNN.oplus (Multiset.map (fun v => GNN.ψ (GNN.X u, GNN.X v) i) (N G u).val)

def h (u : U) : Fin (GraphNeuralNetwork.k R σ) → R := GNN.φ (GNN.X u, msg σ GNN.toDigraph GNN u)

/-- An example of a message function where the aggregator is sum. -/
def message (u : U) : Fin (GraphNeuralNetwork.k R σ) → R := ∑ v in (N G u), (GNN.ψ (GNN.X u, GNN.X v))

/--An example of an update function with message function where the aggregator is sum -/
example (u : U) : Fin (GraphNeuralNetwork.k R σ) → R := GNN.φ (GNN.X u, message σ GNN.toDigraph GNN u)
--This will be given by the pseudocode later
-- def GraphNeuralNetwork.Update [DecidableEq U] [Fintype U] [Semiring R] (GNN : GraphNeuralNetwork R U σ)
--   (state : GNN.State (k:=GNN.k)) (u : U) : GNN.State (k:=GNN.k) :=
--   { update := fun v => if v = u then GNN.oplus  else State.update v }

variable {n m k : ℕ} {R : Type*} [Semiring R] (X : Matrix (Fin n) (Fin k) R)
-- -- Tile a matrix represented as a list of lists along the columns.
-- def tileCols {α : Type} (X : List (List α)) (n : Nat) : List (List α) :=
--   X.map (λ row => List.join (List.replicate n row))

def exampleMatrix : List (List Nat) :=
  [[1, 2], [3, 4]]
-- def tiledMatrix := tileCols exampleMatrix 2
-- #eval tiledMatrix
-- /-- Tile a matrix represented as a list of lists along the rows.-/
-- def tileRows {α : Type} (X : List (List α)) (n : Nat) : List (List α) :=
--   List.join (List.replicate n X)
-- def exampleMatrix' : List (List Nat) := [[1, 2], [3, 4]]
-- def tiledMatrixRows := tileRows exampleMatrix' 2
-- #eval tiledMatrixRows

/-- Tile along the column dimension tile (X, 1, n): -/
def tileColsNested {α : Type} (X : List (List α)) (n : Nat) : List (List (List α)) :=
  X.map (λ row => List.replicate n row)

def ArgrcvExample : List (List (List Nat)) := tileColsNested exampleMatrix 3

#eval ArgrcvExample

/-- Tile along the row dimension tile (X, 0, n). -/
def tileRowsNested {α : Type} (X : List (List α)) (n : Nat) : List (List (List α)) :=
  List.replicate n X

def ArgsndExample := tileRowsNested exampleMatrix 3

#eval ArgsndExample

/-- A general tiling function for lists. -/
def tilelst {α : Type} (A : List α) (reps : List Nat) : List α :=
  if reps.all (· == 1) then A
  else
    let totalReps := reps.foldl (· * ·) 1
    List.join (List.replicate totalReps A)

#eval tilelst [1, 2, 3] [2]
#eval tilelst [1, 2, 3] [1, 2, 3]

def ψ' (argsnd argrcv : List ℕ) : List ℕ := List.zipWith (· + ·) argsnd argrcv

#eval ψ' [1, 2, 3] [4, 5, 6]

def φ' (msgs : List ℕ) : List ℕ := msgs.map (λ x => x * 2)

#eval φ' (ψ' [1, 2, 3] [4, 5, 6])

def aggregateMessages (msgs : List (List ℕ)) : List ℕ :=
  msgs.map (λ msgList => msgList.sum)

#eval aggregateMessages [[1, 2], [3, 4]]

def computeLatentFeaturesFin (X : List (List ℕ)) (n : Nat) : List (List ℕ) := by

  let Argsnd := tileColsNested X n

  let Argrcv := tileRowsNested X n

  let msgs := List.map (λ u =>
    List.map (λ (v : Fin Argrcv.length) =>
      ψ' (Argsnd.get u |>.get! v) (Argrcv.get v |>.get! u)
    ) (List.finRange Argrcv.length)
  ) (List.finRange Argsnd.length)

  let aggregatedMsgs := msgs.map (λ m => aggregateMessages m)

  let latentFeatures := aggregatedMsgs.map (λ aggMsg => φ' aggMsg)

  exact latentFeatures
-- Example for testing the updated function:
#eval computeLatentFeaturesFin [[1, 2], [3, 4]] 3
--(H : Matrix (Fin n) (Fin m) ℝ)

def ψ (x y : Fin n → R) : Fin n → R → Fin n → R → Fin m → R := sorry

def φ (msgs : Fin m → ℝ) : Fin m → R → Fin m → Fin m → ℝ := sorry

def tileColsVecs {α : Type} (X : List (List α)) (n : Nat) : List (List α) :=
  X.map (λ row => List.join (List.replicate n row))

def replicateFin : (n : Nat) → (a : ℝ) → Fin n → ℝ
  | 0,   _ => fun _ => 0
  | n+1, a => fun _ => a

#eval replicateFin 4 5 3
#eval List.replicate 4 5
#check Vector.ofFn

def Arg_snd : Matrix (Fin2 n × Fin2 n) (Fin k) ℝ := fun u => replicateFin k (u.1.toNat)

def Arg_rcv : Matrix (Fin2 n × Fin2 n) (Fin k) ℝ := sorry
--The latent features is what we want to get out of the GNN for fins
def pseudocode : Matrix (Fin n) (Fin m) R := by {

  let msgs (Arg_snd Arg_rcv : Matrix (Fin n × Fin n) (Fin k) R) :
      Matrix (Fin n × Fin n) (Fin m) R := sorry
  sorry
}
