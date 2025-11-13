/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic

import PolyML.Monoidal.DSL
import PolyML.Monoidal.BagInType

open Mathlib Finset

/-
A `NeuralNetwork` models a neural network with:

- `R`: Type for weights and activations.
- `U`: Type for neurons.
- `[Zero R]`: `R` has a zero element.

It extends `Digraph U` and includes the network's architecture, activation functions, and constraints.
-/
structure NeuralNetwork (R U : Type) [Zero R] extends Digraph U where
  /-- Input neurons. -/
  (Ui Uo Uh : Set U)
  /-- There is at least one input neuron. -/
  (hUi : Ui ≠ ∅)
  /-- There is at least one output neuron. -/
  (hUo : Uo ≠ ∅)
  /-- All neurons are either input, output, or hidden. -/
  (hU : Set.univ = (Ui ∪ Uo ∪ Uh))
  /-- Hidden neurons are not input or output neurons. -/
  (hhio : Uh ∩ (Ui ∪ Uo) = ∅)
  /-- Dimensions of input vectors for each neuron. -/
  (κ1 κ2 : U → ℕ)
  /-- Computes the net input to a neuron. -/
  (fnet : ∀ u : U, (U → R) → (U → R) → Vector R (κ1 u) → R)
  /-- Computes the activation of a neuron. -/
  (fact : ∀ u : U, R → R → Vector R (κ2 u) → R) -- R_current_activation, R_net_input, params
  /-- Computes the final output of a neuron. -/
  (fout : ∀ _ : U, R → R)
  /-- Predicate on activations. -/
  (pact : R → Prop)
  /-- Predicate on weight matrices. -/
  (pw : Matrix U U R → Prop)
  /-- If all activations satisfy `pact`, then the activations computed by `fact` also satisfy `pact`. -/
  (hpact : ∀ (w : Matrix U U R) (_ : ∀ u v, ¬ Adj u v → w u v = 0) (_ : pw w)
   (σ : (u : U) → Vector R (κ1 u)) (θ : (u : U) → Vector R (κ2 u)) (current_neuron_activations : U → R),
  (∀ u_idx : U, pact (current_neuron_activations u_idx)) → -- Precondition on all current activations
  (∀ u_target : U, pact (fact u_target (current_neuron_activations u_target) -- Pass current_act of target neuron
                               (fnet u_target (w u_target)
                               (fun v => fout v (current_neuron_activations v)) (σ u_target))
                               (θ u_target))))

variable {R U : Type} [Zero R]

/-- `Params` is a structure that holds the parameters for a neural network `NN`. -/
structure Params (NN : NeuralNetwork R U) where
  (w : Matrix U U R)
  (hw : ∀ u v, ¬ NN.Adj u v → w u v = 0)
  (hw' : NN.pw w)
  (σ : ∀ u : U, Vector R (NN.κ1 u))
  (θ : ∀ u : U, Vector R (NN.κ2 u))

namespace NeuralNetwork

structure State (NN : NeuralNetwork R U) where
  act : U → R
  hp : ∀ u : U, NN.pact (act u)

/-- Extensionality lemma for neural network states -/
@[ext]
lemma ext {R U : Type} [Zero R] {NN : NeuralNetwork R U}
    {s₁ s₂ : NN.State} : (∀ u, s₁.act u = s₂.act u) → s₁ = s₂ := by
  intro h
  cases s₁
  cases s₂
  simp only [NeuralNetwork.State.mk.injEq]
  apply funext
  exact h

namespace State

variable {NN : NeuralNetwork R U} (wσθ : Params NN) (s : NN.State)

def out (u : U) : R := NN.fout u (s.act u)
def net (u : U) : R := NN.fnet u (wσθ.w u) (fun v => s.out v) (wσθ.σ u)
def onlyUi : Prop := ∀ u : U, ¬ u ∈ NN.Ui → s.act u = 0

variable [DecidableEq U]

def Up {NN_local : NeuralNetwork R U} (s : NN_local.State) (wσθ : Params NN_local) (u_upd : U) : NN_local.State :=
  { act := fun v => if v = u_upd then
                      NN_local.fact u_upd (s.act u_upd)
                        (NN_local.fnet u_upd (wσθ.w u_upd) (fun n => s.out n) (wσθ.σ u_upd))
                        (wσθ.θ u_upd)
                    else
                      s.act v,
    hp := by
      intro v_target
      rw [ite_eq_dite]
      split_ifs with h_eq_upd_neuron
      · exact NN_local.hpact wσθ.w wσθ.hw wσθ.hw' wσθ.σ wσθ.θ s.act s.hp u_upd
      · exact s.hp v_target
  }

def workPhase (extu : NN.State) (_ : extu.onlyUi) (uOrder : List U) : NN.State :=
  uOrder.foldl (fun s_iter u_iter => s_iter.Up wσθ u_iter) extu

def seqStates (useq : ℕ → U) : ℕ → NeuralNetwork.State NN
  | 0 => s
  | n + 1 => .Up (seqStates useq n) wσθ (useq n)

def isStable : Prop :=  ∀ (u : U), (s.Up wσθ u).act u = s.act u

end State
end NeuralNetwork

-- We assume the category has products, which is standard for modeling this kind of computation.
-- This lets us pair the "state" and the "list" to feed into the fold operation.
universe u v

namespace CategoryTheory
open Category Opposite MonoidalCategory Limits list NNO

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [WithBags C] [ListArithmetic C]

open NeuralNetwork

-- Assume the necessary types from the NN definition exist as objects in our category C
variable (State_as_obj U_as_obj : C)

namespace Bridge

-- The `update_morph` variable is declared here, in the context.
variable (update_morph : State_as_obj ⊗ U_as_obj ⟶ State_as_obj)

-- We no longer need the separate `workPhase_program` definition.

def workPhase_executable_morphism
    (uOrder_morph : 𝟙_ C ⟶ list U_as_obj)
    (initial_state_morph : 𝟙_ C ⟶ State_as_obj) :
    (𝟙_ C ⟶ State_as_obj) :=
  -- Directly construct the DSL program here.
  let neuron_list_prog : ListDSL (𝟙_ C) U_as_obj :=
    .ofMorph uOrder_morph
  let prog : ListDSL (𝟙_ C) State_as_obj :=
    .foldl update_morph initial_state_morph neuron_list_prog

  -- Evaluate the program and extract the head element
  prog.eval ≫ (by {
    sorry
    --exact list.head (C:=C)
  })


open Mathlib Finset

variable {R U : Type} [Zero R]

/-- Two neurons `u` and `v` are connected in the graph if `w u v` is not zero. -/
def Matrix.Adj (w : Matrix U U R) : U → U → Prop := fun u v => w u v ≠ 0

/-- `Matrix.w` returns the value of the matrix `w` at position `(u, v)` if `u` and `v` are connected. -/
def Matrix.w (w : Matrix U U R) : ∀ u v : U, Matrix.Adj w u v → R := fun u v _ => w u v

/-- A 3x3 matrix of rational numbers. --/
def test.M : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of ![![0,0,4], ![1,0,0], ![-2,3,0]]

def test : NeuralNetwork ℚ (Fin 3) where
  Adj := Matrix.Adj test.M
  Ui := {0,1}
  Uo := {2}
  hU := by
     ext x
     simp only [Set.mem_univ, Fin.isValue, Set.union_singleton,
       Set.union_empty, Set.mem_insert_iff,
       Set.mem_singleton_iff, true_iff]
     revert x
     decide
  Uh := ∅
  hUi := Ne.symm (Set.ne_insert_of_notMem {1} fun a ↦ a)
  hUo := Set.singleton_ne_empty 2
  hhio := by
    simp only [Fin.isValue, Set.union_singleton, Set.empty_inter]
  pw W := True
  κ1 u := 0
  κ2 u := 1
  fnet u w pred σ := ∑ v, w v * pred v
  fact u input θ := if input ≥ θ then 1 else 0
  fout u act := act
  pact u := True
  hpact w _ _ σ θ _ pact u := pact u

def wθ : Params test where
  w := Matrix.of ![![0,0,4], ![1,0,0], ![-2,3,0]]
  θ u := ⟨#[1], by
    simp only [List.size_toArray, List.length_cons, List.length_nil, _root_.zero_add]
    unfold test
    simp only⟩
  σ _ := Vector.emptyWithCapacity 0
  hw u v hv := by by_contra h; exact hv h
  hw' := by simp only [test]

instance : Repr (NeuralNetwork.State test) where
  reprPrec state _ :=
   ("acts: " ++ repr (state.act)) ++ ", outs: " ++
        repr (state.out) ++ ", nets: " ++ repr (state.net wθ)

/--
`test.extu` is the initial state for the `test` neural network with activations `[1, 0, 0]`.
-/
def test.extu : test.State := {act := ![1,0,0], hp := fun _ => trivial}

lemma zero_if_not_mem_Ui : ∀ u : Fin 3,
  ¬ u ∈ ({0,1} : Finset (Fin 3)) → test.extu.act u = 0 := by decide

/--If `u` is not in the input neurons `Ui`, then `test.extu.act u` is zero.-/
lemma test.onlyUi : test.extu.onlyUi := by {
  intros u hu
  apply zero_if_not_mem_Ui u
  simp only [Fin.isValue, mem_insert, mem_singleton, not_or]
  exact not_or.mp hu}

/-The workphase for the asynchronous update of the sequence of neurons u3 , u1 , u2 , u3 , u1 , u2 , u3. -/
#eval NeuralNetwork.State.workPhase wθ test.extu test.onlyUi [2,0,1,2,0,1,2]

/-The workphase for the asynchronous update of the sequence of neurons u3 , u2 , u1 , u3 , u2 , u1 , u3. -/
#eval NeuralNetwork.State.workPhase wθ test.extu test.onlyUi [2,1,0,2,1,0,2]

/-!
 Executing workPhase
-/
def update_func : test.State × Fin 3 → test.State :=
  fun (s, u) => s.Up wθ u

def initial_state_func : PUnit → test.State :=
  fun _ => test.extu

-- This function takes a list and returns the corresponding morphism `PUnit → List (Fin 3)`.
def uOrder_morph (order : List (Fin 3)) : 𝟙_ Type ⟶ list (Fin 3) :=
  fun _ => ⟨order, PUnit.unit⟩

-- Example 1 - fix the argument order
#eval (workPhase_executable_morphism (C:=Type)
  (State_as_obj := test.State) (U_as_obj:=Fin 3) (update_morph:=update_func)
    (uOrder_morph [2,0,1,2,0,1,2]) initial_state_func) PUnit.unit

end Bridge
end CategoryTheory
