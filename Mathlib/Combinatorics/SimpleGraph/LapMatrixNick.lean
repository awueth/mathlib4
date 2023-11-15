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



/--
If x ∈ {-1, 1}^V ∩ ker(L), then vector_to_vertices has cut 0
theorem ker_cut_zero (f : V → ℤ) :
  cut G (vector_to_vertices f) = Function.const V ℤ 0 := by
  sorry
--/



-- If s ⊂ V has cut 0, the vertices_to_vector ∈ ker(L)
theorem cut_zero_ker (s : Finset V) (h_s : cut G s = 0) :
  mulVec (G.lapMatrix ℤ) (vertices_to_vector s) = 0 := by

  -- Check that the entry at v is zero
  ext v
  simp only [Pi.zero_apply]

  -- Write matrix multiplication as sum
  unfold mulVec dotProduct lapMatrix
  simp only [sub_apply]

  -- Plug in definitions
  unfold degMatrix adjMatrix
  simp only [of_apply]

  -- Split sum into two parts; one over s and one over sᶜ
  rw [← Finset.sum_compl_add_sum s]

  have h_in_sc_minusone : ∀ w : V, w ∈ sᶜ  → vertices_to_vector s w = -1
  · intro w hw
    unfold vertices_to_vector
    rw [if_neg]
    rw [← Finset.mem_compl]
    exact hw

  have h_in_s_one : ∀ w : V, w ∈ s → vertices_to_vector s w = 1
  · intro w hw
    unfold vertices_to_vector
    rw [if_pos]
    exact hw

  have h_sum_sc : ∑ w in sᶜ, ((if v = w then ↑(degree G v) else 0) - if Adj G v w then 1 else 0) * vertices_to_vector s w = ∑ w in sᶜ, ((if v = w then ↑(degree G v) else 0) - if Adj G v w then 1 else 0) * (-1 : ℤ)
  · apply Finset.sum_congr rfl
    intro w hw
    rw [h_in_sc_minusone w hw]

  have h_sum_s : ∑ w in s, ((if v = w then ↑(degree G v) else 0) - if Adj G v w then 1 else 0) * vertices_to_vector s w = ∑ w in s, ((if v = w then ↑(degree G v) else (0 : ℤ)) - if Adj G v w then 1 else 0)
  · apply Finset.sum_congr rfl
    intro w hw
    rw [h_in_s_one w hw]
    simp only [mul_one]

  rw [h_sum_sc, h_sum_s]

  have h_minus_sum_eq_sum_minus : ∑ w in sᶜ, ((if v = w then ↑(degree G v) else 0) - if Adj G v w then 1 else 0) * (-1 : ℤ) = - ∑ w in sᶜ, ((if v = w then ↑(degree G v) else (0 : ℤ)) - if Adj G v w then 1 else 0)
  · simp

  rw [h_minus_sum_eq_sum_minus]

  by_cases h_v : v ∈ s
  ·
    sorry
  ·
    sorry




-- SimpleGraph.irrefl
