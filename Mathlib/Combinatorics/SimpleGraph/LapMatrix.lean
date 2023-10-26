import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

open BigOperators Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def degMatrix : Matrix V V ℝ :=
  fun a b => if a = b then G.degree a else 0

def lapMatrix : Matrix V V ℝ := degMatrix G - G.adjMatrix ℝ

def lapBilinForm := Matrix.toBilin' (lapMatrix G)

def cut : Finset V → ℕ :=
  fun s => ∑ i in s, ∑ j in sᶜ, (if G.Adj i j then 1 else 0)

variable (s : Finset V)

def special_vector : V → ℝ := fun v => if v ∈ s then 1 else -1

lemma square (x : V) : (special_vector s x) * (special_vector s x) = 1 := by
  unfold special_vector
  simp
  sorry

/- x^tLx = 4*cut(S) -/
theorem asdf :
  lapBilinForm G (special_vector s) (special_vector s) = 4*cut G s := by
  unfold lapBilinForm
  rw [Matrix.toBilin'_apply']
  unfold lapMatrix
  rw [sub_mulVec]
  simp
  unfold mulVec dotProduct
  simp [Finset.mul_sum]
  unfold degMatrix
  simp [mul_comm, ← mul_assoc, square]
  rw [sum_degrees_eq_twice_card_edges]
  sorry
