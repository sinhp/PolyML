import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fin.Fin2
import Mathlib.Data.Matrix.PEquiv

set_option linter.unusedVariables false

open Mathlib Finset

universe u v

variable {R U : Type*} (σ : Equiv.Perm U) (X : Matrix U (Fin k) R)

variable (G : Digraph U) [DecidableRel G.Adj] [Fintype U] [DecidableEq U]

/--the 1-hop neighborhood including the node itself-/
def Neigh (u : U) : Finset U := {v | G.Adj v u ∨ G.Adj u v}.toFinset ∪ {u}

def XN (u : U) [Fintype (Fin k → R)] : Multiset (Fin k → R) := (Neigh G u).val.map (X ·)

def Digraph.pred (u : U) : Finset U := {v | G.Adj v u}.toFinset
variable {R U : Type*} [Fintype U] [DecidableEq U]  {n m k : ℕ} [Semiring R]

/-- Holds GNN parameters, including the input feature matrix X. -/
structure GNN_Parameters (R U : Type*) (k m : ℕ) where
  X : Matrix U (Fin k) R
  -- In a real model, learnable weights would also be here.

/-- The fixed computational architecture of the GNN. -/
structure GNN_Architecture (R U : Type*) (k m : ℕ) where
  /-- The message function ψ : ℝᵏ × ℝᵏ → ℝᵐ -/
  ψ (params : GNN_Parameters R U k m) (sender_features : Fin k → R) (receiver_features : Fin k → R) : Fin m → R
  /-- The aggregation function ⊕, which must be permutation-invariant. -/
  aggregate : Multiset (Fin m → R) → (Fin m → R)
  /-- The update function φ : ℝᵐ → ℝᵐ -/
  φ (params : GNN_Parameters R U k m) (aggregated_message : Fin m → R) : Fin m → R

/--
A structure to hold the input data for a single GNN forward pass.
-/
structure GraphData (U : Type*) (k : ℕ) where
  /-- The graph topology (who is connected to whom). -/
  graph : Digraph U
  /-- The node feature matrix X, of shape |U| × k. -/
  X : Matrix U (Fin k) R

/--
Performs one forward pass of a GNN layer using neighbor-only message passing.
-/
def gnnForwardPass
    (arch : GNN_Architecture R U k m)
    (params : GNN_Parameters R U k m)
    (data : GraphData (R:=R) U k) [DecidableRel data.graph.Adj] :
    Matrix U (Fin m) R :=

  -- The function still computes the new feature matrix H.
  fun u => -- For each node `u`...

    -- 1. Compute all possible messages (this can be seen as a pre-computation).
    let msgs : Matrix U U (Fin m → R) :=
      fun sender receiver => arch.ψ params (data.X sender) (data.X receiver)

    -- 2. Gather incoming messages from NEIGHBORS ONLY.
    -- MODIFIED: Get the set of predecessors for node `u` from the graph.
    let predecessors := data.graph.pred u

    -- MODIFIED: Map over the predecessors, not all nodes.
    let incoming_messages : Multiset (Fin m → R) :=
      predecessors.val.map (fun v => msgs v u)

    -- 3. Aggregate the messages from the neighborhood.
    let aggregated_message := arch.aggregate incoming_messages

    -- 4. Apply the update function.
    arch.φ params aggregated_message

-- Add Repr instance to allow #eval to print the output matrix.
instance {n m : ℕ} [Repr α] : Repr (Matrix (Fin n) (Fin m) α) where
  reprPrec m _ := repr (List.ofFn fun i => List.ofFn fun j => m i j)

abbrev Nodes := Fin 2

def K : ℕ := 2  -- Input feature dimension
def M : ℕ := 3  -- Latent (message) feature dimension

-- This is the fixed architecture for our example GNN.
def myGNN_Arch : GNN_Architecture ℕ Nodes K M where
  ψ := fun _ sender_vec receiver_vec i =>
         if h : i.val < K then
           sender_vec ⟨i.val, h⟩ + receiver_vec ⟨i.val, h⟩
         else
           0
  aggregate := fun msgs => Multiset.sum msgs -- Aggregation is summation
  φ := fun _ agg_msg i => agg_msg i + agg_msg i     -- Update is doubling the vector

-- These are the parameters and input data for this specific run.
def X_example : Matrix Nodes (Fin K) ℕ :=
  fun i j => if i.val = 0 then j.val + 1 else j.val + 3 -- X = [[1, 2], [3, 4]]

def myGNN_Params : GNN_Parameters ℕ Nodes K M where
  X := X_example

-- Example graph: no edges (empty adjacency)
def trivialDigraph : Digraph Nodes where
  Adj _ _ := False

-- FIX: Provide a direct, COMPUTABLE proof that the relation is decidable.
instance : DecidableRel trivialDigraph.Adj :=
  fun _ _ => isFalse (by exact fun a ↦ a)

def exampleGraphData : GraphData Nodes (R:=ℕ) K where
  graph := trivialDigraph
  X := X_example

instance : DecidableRel exampleGraphData.graph.Adj := by {exact
  instDecidableRelNodesAdjTrivialDigraph}

-- Now the final #eval is fully computable and doesn't need the `!` hint.
#eval gnnForwardPass myGNN_Arch myGNN_Params exampleGraphData


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

-- instance : DecidableRel lineGraphData.graph.Adj := by {
--   sorry
-- }

-- #eval gnnForwardPass myGNN_Arch myGNN_Params' lineGraphData
