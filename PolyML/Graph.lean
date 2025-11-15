/-
Copyv (c) 2025 Sina Hazratpour. All vs reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/


import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_
import PolyML.Monoidal.Fin

noncomputable section

namespace CategoryTheory

open Category Limits CartesianMonoidalCategory MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [NNO C] [ChosenPullbacks C]
  [HasBinaryCoproducts C]

class GraphObj (V : C) where
  E : C
  source : E ⟶ V
  target : E ⟶ V
  finite_neighborhood : FiniteFibres (lift (source) (target) ≫ snd _ _)

namespace GraphObj

/-- The sum of two graphs objects. -/
def sum {V₁ V₂ : C} (G₁ : GraphObj V₁) (G₂ : GraphObj V₂) : GraphObj (V₁ ⨿ V₂) where
  E := G₁.E ⨿ G₂.E
  source := coprod.map G₁.source G₂.source
  target := coprod.map G₁.target G₂.target
  finite_neighborhood := by
      sorry

/-- The product of two graph objects. -/
def prod {V₁ V₂ : C} (G₁ : GraphObj V₁) (G₂ : GraphObj V₂) : GraphObj (V₁ ⊗ V₂) where
  E := G₁.E ⊗ G₂.E
  source := G₁.source ⊗ₘ G₂.source
  target := G₁.target ⊗ₘ G₂.target
  finite_neighborhood := by
    sorry

/-- The empty graph object on vertex object V. -/
def empty [HasInitial C] (V : C) : GraphObj V where
  E := ⊥_ C
  source := IsInitial.to (initialIsInitial) V
  target := IsInitial.to (initialIsInitial) V
  finite_neighborhood := by
    sorry

/-- The mirror opposite of a graph object, obtained by swapping source and target. -/
def opposite {V : C} (G : GraphObj V) : GraphObj V where
  E := G.E
  source := G.target
  target := G.source
  finite_neighborhood := by
    sorry

/-- The symmetrization of a graph object, obtained by adding a reversed edge for each edge. -/
def symmetrize {V : C} (G : GraphObj V) : GraphObj V where
  E := G.E ⨿ G.E
  source := coprod.desc G.source G.target
  target := coprod.desc G.target G.source
  finite_neighborhood := by
    sorry

/-- A vertex is isolated if there are no edges connected to it. -/
def isIsolatedVertex {V : C} (G : GraphObj V) : V ⟶ (bool : C)  := sorry

end GraphObj

#check Digraph

variable (C)
class Graph where
  V : C
  [graphObj : GraphObj V]

class FiniteGraph extends Graph C where
  [finEnumVertices : FinEnum V]

instance [FiniteGraph C] : Graph C := by
  infer_instance

namespace Graph

variable {C}

variable (G : Graph C)

abbrev vertices : C := G.V

abbrev edges : C :=  G.graphObj.E

def source : G.edges ⟶ G.vertices := G.graphObj.source

def target : G.edges ⟶ G.vertices := G.graphObj.target

def adj : (vertices G) ⊗ (vertices G) ⟶ bool := sorry

end Graph

def DiGraph := {G : Graph C // Mono (Graph.adj G)}

namespace DiGraph

variable {C}

abbrev vertices (G : DiGraph C) : C := Graph.vertices G.1

abbrev edges (G : DiGraph C) : C := Graph.edges G.1

abbrev source (G : DiGraph C) : edges G ⟶ vertices G := Graph.source G.1

abbrev target (G : DiGraph C) : edges G ⟶ vertices G := Graph.target G.1

variable (G : DiGraph C)

end DiGraph



end CategoryTheory
