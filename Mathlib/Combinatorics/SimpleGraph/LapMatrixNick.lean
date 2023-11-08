import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Vector



open Matrix SimpleGraph BigOperators Vector


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]



-- Define degree matrix of a graph
def SimpleGraph.degMatrix (R : Type*) [Ring R] :
  Matrix V V R := of fun a b ↦ if a = b then (G.degree a : R) else 0

-- Define Laplacian matrix of a graph
def SimpleGraph.lapMatrix (R : Type*) [Ring R] :
  Matrix V V R := G.degMatrix R - G.adjMatrix R

-- Number of edges between a vertex set and its complement
def cut :
  Finset V → ℕ := fun s ↦ ∑ v in s, ∑ w in sᶜ, (if G.Adj v w then 1 else 0)

-- From subset of vertices to vector (as map) in {-1, 1}^V
def vertices_to_vector (s : Finset V) :
  V → ℤ := fun v ↦ (if v ∈ s then 1 else -1)

-- From vector (as map) in {-1, 1}^V to subset of vertices
def vector_to_vertices (f : V → ℤ) :
  Set V := {v | f v = 1}



-- If x ∈ {-1, 1}^V ∩ ker(L), then vector_to_vertices has cut 0



-- If s ⊂ V has cut 0, the vertices_to_vector ∈ ker(L)
