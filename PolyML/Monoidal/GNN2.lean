import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import PolyML.Monoidal.DSL

/-! # Pseudocode implementation of GNN
In this file, we implement in Lean the pseudocode for the GNN corresponding to the second
Diagram 7 page 12 in
  `Graph Neural Networks are Dynamic Programmers`.

TODO: Implement it using the DSL.
TODO: Formalize the correspondence with polynomial spans.
 -/

set_option linter.unusedVariables false

open Mathlib Finset

universe u v

variable {R U : Type*} [Fintype U] [DecidableEq U]  {n m k : ℕ} [Semiring R]

structure GNN_Parameters (R U : Type*) (k m : ℕ) where
  X : Matrix U (Fin k) R

structure GNN_Architecture_V2 (R U : Type*) (k m : ℕ) where
  ψ_edge (params : GNN_Parameters R U k m) (sender receiver : Fin k → R) : Fin m → R
  ψ_triplet (params : GNN_Parameters R U k m) (f₁ f₂ f₃ : Fin k → R) : Fin m → R
  aggregate_node : Multiset (Fin m → R) → (Fin m → R)
  aggregate_edge : Multiset (Fin m → R) → (Fin m → R)
  φ_node (params : GNN_Parameters R U k m) (original_features : Fin k → R)
    (agg_msg : Fin m → R) : Fin m → R
  φ_edge (params : GNN_Parameters R U k m) (agg_msg : Fin m → R) : Fin m → R

structure GraphData (R U: Type*) [Zero R] [One R] [DecidableEq R] (k : ℕ) where
  AdjMatrix : Matrix U U R
  X : Matrix U (Fin k) R

def getPredecessorsFromMatrix [DecidableEq R] (data : GraphData R U k) (u : U) : Finset U :=
  (Finset.univ : Finset U).filter (fun v => data.AdjMatrix v u ≠ 0)

/--
Returns (H, M): the new node features and new edge features.
-/
def gnnForwardPassV2 [DecidableEq R]
    (arch : GNN_Architecture_V2 R U k m)
    (params : GNN_Parameters R U k m)
    (data : GraphData R U k) :
    (Matrix U (Fin m) R) × (Matrix (U × U) (Fin m) R) :=

  -- Compute edge and triplet messages as before.
  let msgs_edge := fun (u, v) => arch.ψ_edge params (data.X u) (data.X v)
  let msgs_triplet := fun (u, v, w) => arch.ψ_triplet params (data.X u) (data.X v) (data.X w)

  -- Compute the new node features, H, using NEIGHBOR-ONLY aggregation.
  let H : Matrix U (Fin m) R := fun u =>
      -- Get the specific neighbors for node `u` from the adjacency matrix
      let predecessors := getPredecessorsFromMatrix data u
      -- Gather incoming edge messages only from those neighbors
      let incoming_edge_msgs := predecessors.val.map (fun v => msgs_edge (v, u))
      let aggregated_node_msg := arch.aggregate_node incoming_edge_msgs
      -- Update using the original features and the aggregated message
      arch.φ_node params (data.X u) aggregated_node_msg

  -- Compute the new edge features, M (still using all-pairs for triplets per the pseudocode)
  let M : Matrix (U × U) (Fin m) R := fun (u, v) =>
      let incoming_triplet_msgs := (Finset.univ : Finset U).val.map (fun w => msgs_triplet (u, v, w))
      let aggregated_edge_msg := arch.aggregate_edge incoming_triplet_msgs
      arch.φ_edge params aggregated_edge_msg

  (H, M)


instance {n m : ℕ} [Repr α] : Repr (Matrix (Fin n) (Fin m) α) where
  reprPrec m _ := repr (List.ofFn fun i => List.ofFn fun j => m i j)

instance {n n' m : ℕ} [Repr α] : Repr (Matrix (Fin n × Fin n') (Fin m) α) where
  reprPrec m _ :=
    let all_row_indices := do
      let i ← List.finRange n
      let j ← List.finRange n'
      pure (i, j)
    let list_of_rows := all_row_indices.map (fun i => List.ofFn (m i))
    repr list_of_rows

--Example
abbrev Nodes := Fin 2
def K : ℕ := 2
def M : ℕ := 3

def myGNN_Arch : GNN_Architecture_V2 ℕ Nodes K M where
  ψ_edge    := fun _ sender receiver i =>
                 if h:i.val < K then sender ⟨i.val,h⟩ + receiver ⟨i.val,h⟩ else 0
  ψ_triplet := fun _ f₁ f₂ f₃ i =>
                 if h:i.val < K then f₁ ⟨i.val,h⟩ + f₂ ⟨i.val,h⟩ + f₃ ⟨i.val,h⟩ else 0
  aggregate_node := fun msgs => Multiset.sum msgs
  aggregate_edge := fun msgs => Multiset.sum msgs
  φ_node    := fun _ original agg i =>
                 if h:i.val < K then original ⟨i.val,h⟩ + agg i else agg i
  φ_edge    := fun _ agg i =>
                 agg i + agg i

def X_example : Matrix Nodes (Fin K) ℕ :=
  fun i j => if i.val = 0 then j.val + 1 else j.val + 3 -- X = [[1, 2], [3, 4]]

def AdjMatrix_example : Matrix Nodes Nodes ℕ :=
  fun i j => match (i.val, j.val) with
    | (0, 1) | (1, 0) => 1
    | _ => 0

def myGNN_Params : GNN_Parameters ℕ Nodes K M where
  X := X_example

def exampleGraphData : GraphData ℕ Nodes K where
  AdjMatrix := AdjMatrix_example
  X := X_example

#eval gnnForwardPassV2 myGNN_Arch myGNN_Params exampleGraphData
