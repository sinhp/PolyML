import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fin.Fin2
import Mathlib.Data.Matrix.PEquiv

set_option linter.unusedVariables false

open Mathlib Finset

universe u v

variable {n m k : ℕ} {R : Type*} [Semiring R] (X : Matrix (Fin n) (Fin k) R)
-- -- Tile a matrix represented as a list of lists along the columns.
-- def tileCols {α : Type} (X : List (List α)) (n : Nat) : List (List α) :=
--   X.map (λ row => List.join (List.replicate n row))

def exampleMatrix : List (List Nat) :=
  [[1, 2], [3, 4]]

/-- Tile along the column dimension tile (X, 1, n): -/
def tileColsNested {α : Type} (X : List (List α)) (n : Nat) : List (List (List α)) :=
  X.map (fun row => List.replicate n row)

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
    List.flatten (List.replicate totalReps A)

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

def tileColsVecs {α : Type} (X : List (List α)) (n : Nat) : List (List α) :=
  X.map (λ row => List.flatten (List.replicate n row))

def replicateFin : (n : Nat) → (a : R) → Fin n → R
  | 0,   _ => fun _ => 0
  | n+1, a => fun _ => a

#eval replicateFin 4 5 3
#eval List.replicate 4 5
#check Vector.ofFn

def Arg_snd : Matrix (Fin n × Fin n) (Fin k) R := fun u => replicateFin k (u.1.toNat)

def Arg_rcv : Matrix (Fin n × Fin n) (Fin k) R := fun u => replicateFin k (u.2.toNat)

-- Example with Arg_rcv
def example_Arg_rcv : Matrix (Fin 3 × Fin 3) (Fin 2) ℕ := Arg_rcv



-- Example graph: no edges (empty adjacency)
def trivialDigraph : Digraph Nodes where
  Adj _ _ := False

-- FIX: Provide a direct, COMPUTABLE proof that the relation is decidable.
-- instance : DecidableRel trivialDigraph.Adj :=
--   fun _ _ => isFalse (by exact fun a ↦ a)
-- -- We'll work with 3 nodes for this example.
-- def N : ℕ := 3

-- /-- An adjacency relation for a 3-node line graph: 0 → 1 → 2. -/
-- def lineGraphAdj : Nodes → Nodes → Prop :=
--   fun u v => (u.1 = 0 ∧ v.1 = 1) ∨ (u.1 = 1 ∧ v.1 = 2)

-- -- We also need a *computable* way to decide this relation.
-- -- Lean can figure this out automatically.
-- -- A new 3x2 feature matrix for our 3 nodes.
-- def X_3_nodes : Matrix Nodes (Fin K) ℕ :=
--   fun i j => (i.val + 1) * (j.val + 1) -- e.g., [[1,2], [2,4], [3,6]]

-- def myGNN_Params' : GNN_Parameters ℕ Nodes K M where
--   X := X_3_nodes
-- -- Bundle the graph and features into a single GraphData object.
-- def lineGraphData : GraphData Nodes (R:=ℕ) K where
--   graph := { Adj := lineGraphAdj }
--   X := X_3_nodes

-- #eval gnnForwardPass myGNN_Arch myGNN_Params' lineGraphData

def N : ℕ := 3
abbrev Node := Fin N

-- An adjacency matrix for the graph 0 → 1 → 2
def lineGraphMatrix : Matrix Node Node ℕ := sorry

-- This matrix looks like:
-- [[0, 1, 0],
--  [0, 0, 1],
--  [0, 0, 0]]

/-- Creates an adjacency relation from a matrix. An edge exists if the entry is non-zero. -/
def adjRelFromMatrix (A : Matrix Node Node ℕ) : Node → Node → Prop :=
  fun u v => A u v ≠ 0

#check Matrix.IsAdjMatrix

--(σ : Equiv.Perm U) (X : Matrix U (Fin k) R)

--variable (G : Digraph U) [DecidableEq R] [DecidableRel G.Adj] [Fintype U] [DecidableEq U]

--/--the 1-hop neighborhood including the node itself-/
--def Neigh (u : U) : Finset U := {v | G.Adj v u ∨ G.Adj u v}.toFinset ∪ {u}

--def XN (u : U) [Fintype (Fin k → R)] : Multiset (Fin k → R) := (Neigh G u).val.map (X ·)

--def Digraph.pred (u : U) : Finset U := {v | G.Adj v u}.toFinset
