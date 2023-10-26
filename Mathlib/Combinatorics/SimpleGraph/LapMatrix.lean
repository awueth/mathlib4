import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

open BigOperators Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def SimpleGraph.degMatrix (R : Type*) [Ring R] : Matrix V V R :=
  of fun a b ↦ if a = b then (G.degree a : R) else 0

def SimpleGraph.lapMatrix (R : Type*) [Ring R] : Matrix V V R := G.degMatrix R - G.adjMatrix R

theorem lapMatrix_mulVec_const : mulVec (G.lapMatrix ℤ) (Function.const V 1) = 0 := by
  unfold lapMatrix
  rw [sub_mulVec]
  ext; simp;
  unfold mulVec dotProduct
  simp only [Pi.one_apply, mul_one]
  unfold degMatrix
  simp only [of_apply, sum_ite_eq, mem_univ, ite_true, sub_self]
  -- Could this be useful: adjMatrix_mulVec_const_apply?

def cut : Finset V → ℕ :=
  fun s => ∑ i in s, ∑ j in sᶜ, (if G.Adj i j then 1 else 0)

variable (s : Finset V)

def indicatorMinusIndicator : V → ℤ := fun v => if v ∈ s then 1 else -1

lemma indicatorMinusIndicator_mul_indicatorMinusIndicator (x y : V) :
  (indicatorMinusIndicator s x) * (indicatorMinusIndicator s y) =
  if ((x ∈ s ∧ y ∈ s) ∨ (x ∈ sᶜ ∧ y ∈ sᶜ)) then 1 else - 1 := by
  unfold indicatorMinusIndicator
  split
  case inl h
  · simp [h]
  case inr h'
  · simp [h']

lemma indicatorMinusIndicator_square (x : V) :
  (indicatorMinusIndicator s x) * (indicatorMinusIndicator s x) = 1 := by
  unfold indicatorMinusIndicator
  split
  repeat simp

/- x^tLx = 4*cut(S) -/
theorem asdf :
  Matrix.toBilin' (G.lapMatrix ℤ) (indicatorMinusIndicator s) (indicatorMinusIndicator s) = 4*cut G s := by
  rw [Matrix.toBilin'_apply']
  unfold lapMatrix
  rw [sub_mulVec]
  simp
  unfold mulVec dotProduct
  simp [Finset.mul_sum]
  unfold degMatrix
  simp [mul_comm, ← mul_assoc, indicatorMinusIndicator_square]
  -- rw [sum_degrees_eq_twice_card_edges]
  simp [indicatorMinusIndicator_mul_indicatorMinusIndicator]
  sorry

theorem main_result : Fintype.card G.ConnectedComponent = Fintype.card V - (G.lapMatrix ℤ).rank := by
  sorry
