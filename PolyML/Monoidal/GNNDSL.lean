import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Matrix.Defs
import PolyML.Monoidal.DSL

/-! # Pseudocode implementation of GNN
In this file, we implement in Lean the pseudocode
for the GNN corresponding to Diagram 7 page 12 in
  `Graph Neural Networks are Dynamic Programmers`.

TODO: Formalize the correspondence with polynomial spans.
 -/

set_option linter.unusedVariables false

open Mathlib Finset

universe u v

variable {R U : Type*} [Fintype U] [DecidableEq U]  {n m k : ℕ} [Semiring R]

/-- Holds GNN parameters, including the input feature matrix X. -/
structure GNN_Parameters (R U : Type*) (k m : ℕ) where
  X : Matrix U (Fin k) R
  -- In a real model, learnable weights would also be here.

/-- The fixed computational architecture of the GNN. -/
structure GNN_Architecture (R U : Type*) (k m : ℕ) where
  /-- The message function ψ : ℝᵏ × ℝᵏ → ℝᵐ -/
  ψ (params : GNN_Parameters R U k m) (sender_features : Fin k → R)
      (receiver_features : Fin k → R) : Fin m → R
  /-- The aggregation function ⊕, which must be permutation-invariant (TODO) -/
  aggregate : Multiset (Fin m → R) → (Fin m → R)
  /-- The update function φ : ℝᵐ → ℝᵐ -/
  φ (params : GNN_Parameters R U k m) (aggregated_message : Fin m → R) : Fin m → R

/--
A structure to hold the input data for a single GNN forward pass.
-/
structure GraphData (U : Type*) (R: Type*) [Zero R] [One R] [DecidableEq R] (k : ℕ) where
  /-- The graph topology. -/
  AdjMatrix : Matrix U U R
  --h : AdjMatrix.IsAdjMatrix
  -- graph : SimpleGraph U := by {
  --   apply Matrix.IsAdjMatrix.toGraph h}
  /-- The node feature matrix X, of shape |U| × k. -/
  X : Matrix U (Fin k) R

def Simple.pred (g: SimpleGraph U) (u : U) [Fintype U]
      [DecidableEq U] [DecidablePred fun v ↦ g.Adj v u] :
   Finset U := Finset.univ.filter (fun v => g.Adj v u)


def getPredecessorsFromMatrix [DecidableEq R] (data : GraphData U R k) (u : U) : Finset U :=
  Finset.univ.filter (fun v => data.AdjMatrix v u ≠ 0)

/--
Performs one forward pass of a GNN layer using neighbor-only message passing
  to compute the new feature matrix H.
-/
def gnnForwardPass [DecidableEq R] (arch : GNN_Architecture R U k m)
    (params : GNN_Parameters R U k m) (data : GraphData (R:=R) U k)  :
  Matrix U (Fin m) R := fun u =>

    -- Compute all possible messages (this can be seen as a pre-computation).
    let msgs : Matrix U U (Fin m → R) :=
      fun sender receiver => arch.ψ params (data.X sender) (data.X receiver)

    -- Get the set of predecessors for node `u` from the adjacency matrix.
    let predecessors := getPredecessorsFromMatrix data u

    -- Map over the predecessors, not all nodes.
    let incoming_messages : Multiset (Fin m → R) :=
      predecessors.val.map (fun v => msgs v u)

    -- Aggregate the messages from the neighborhood.
    let aggregated_message := arch.aggregate incoming_messages

    -- Apply the update function.
    arch.φ params aggregated_message

-- Add Repr instance to allow #eval to print the output matrix.
instance {n m : ℕ} [Repr α] : Repr (Matrix (Fin n) (Fin m) α) where
  reprPrec m _ := repr (List.ofFn fun i => List.ofFn fun j => m i j)

abbrev Nodes := Fin 5

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

def AdjMatrix_example : Matrix Nodes Nodes ℕ :=
  fun i j =>
    match (i.val, j.val) with
    | (0, 1) => 1
    | (1, 0) => 1
    | _      => 0

def myGNN_Params : GNN_Parameters ℕ Nodes K M where
  X := X_example

def exampleGraphData : GraphData Nodes (R:=ℕ) K where
  AdjMatrix := AdjMatrix_example
  --h := by constructor; decide; decide; decide
  X := X_example

#eval gnnForwardPass myGNN_Arch myGNN_Params exampleGraphData

/--
This function contains the GNN update logic for a SINGLE node `u`.
It takes all the graph data as input so it can be mapped over a list of nodes.
-/
def compute_update_for_one_node [DecidableEq R]
    (arch : GNN_Architecture R U k m) (params : GNN_Parameters R U k m)
    (data : GraphData U R k)
    (u : U) : Fin m → R :=
  let predecessors := getPredecessorsFromMatrix data u
  let incoming_messages :=
    predecessors.val.map (fun v => arch.ψ params (data.X v) (data.X u))
  let aggregated_message := arch.aggregate incoming_messages
  arch.φ params aggregated_message

namespace GNN_DSL

abbrev C_concrete := Type

def listOfNodes : List Nodes := [0, 1, 4, 5]  -- nodes indices

open CategoryTheory

open Category Opposite MonoidalCategory Limits list NNO

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [ListArithmetic C] [WithBags C]

/--
This function builds a ListDSL program to perform the GNN forward pass
and then evaluates it.
-/
def gnnForwardPass_via_DSL {R U : Type} {k m : ℕ} [Fintype U]
 [DecidableEq R][DecidableEq U] [Semiring R]
    (arch : GNN_Architecture R U k m) (params : GNN_Parameters R U k m)
    (data : GraphData U R k) (listOfNodes : List U) :
    -- The output is a list of the new feature vectors
    List (Fin m → R) :=

  -- Create a morphism that produces a list of all nodes.
  let all_nodes_morph : 𝟙_ C_concrete ⟶ list U :=
    fun _ => ⟨listOfNodes, PUnit.unit⟩

  -- Build the ListDSL program.
  let nodes_prog : ListDSL (𝟙_ C_concrete) U := .ofMorph all_nodes_morph
  let compute_update_fn : U → (Fin m → R) :=
    compute_update_for_one_node arch params data
  let new_features_prog : ListDSL (𝟙_ C_concrete) (Fin m → R) :=
    nodes_prog.map (compute_update_for_one_node arch params data)

  -- Run the program using the real interpreter.
  (new_features_prog.eval PUnit.unit).1

instance {n} [Repr α] : Repr (Fin n → α) where reprPrec f _ := repr (List.ofFn f)

instance : Repr (List (Fin M → ℕ)) where
  reprPrec l _ := repr l

#eval gnnForwardPass_via_DSL myGNN_Arch myGNN_Params exampleGraphData listOfNodes
