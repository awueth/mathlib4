import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Data.Matrix.Basic

open BigOperators Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


def degMatrix : Matrix V V ℤ :=
  fun a b => if a = b then G.degree a else 0

def lapMatrix : Matrix V V ℤ := degMatrix G - G.adjMatrix ℤ

def cut : Finset V → ℕ :=
  fun s => ∑ i in s, ∑ j in sᶜ, (if G.Adj i j then 1 else 0)

variable (s : Finset V)

#check cut G s

/-
TODO:
theorem : cut G s = 1/4 * x^T * lapMatrix G * x
where x = 1_{S} - 1_{S^c}
-/


/-
Stubid, only works for digraphs
theorem whatever :
  lapMatrix G = (G.incMatrix ℤ * (G.incMatrix ℤ)ᵀ) := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j

  -- Case i = j
  {
    rw [h]
    rw [incMatrix_mul_transpose_diag]
    unfold lapMatrix
    simp
    unfold degMatrix
    simp
  }

  -- Case i ≠ j
  {
    simp [mul_apply, transpose_apply, incMatrix_apply_mul_incMatrix_apply]
    unfold lapMatrix
    unfold degMatrix
    unfold adjMatrix
    simp [h]
    sorry
  }
-/
