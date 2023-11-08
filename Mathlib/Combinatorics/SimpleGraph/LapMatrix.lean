import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

open BigOperators Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def SimpleGraph.degMatrix (R : Type*) [Ring R] : Matrix V V R :=
  of fun a b ↦ if a = b then (G.degree a : R) else 0

def SimpleGraph.lapMatrix (R : Type*) [Ring R] : Matrix V V R := G.degMatrix R - G.adjMatrix R

-- The vector (1,...,1) is in the kernel of the laplacian
theorem lapMatrix_mulVec_const : mulVec (G.lapMatrix ℤ) (Function.const V 1) = 0 := by
  unfold lapMatrix
  rw [sub_mulVec]
  ext; simp;
  unfold mulVec dotProduct
  simp only [Pi.one_apply, mul_one]
  unfold degMatrix
  simp only [of_apply, sum_ite_eq, mem_univ, ite_true, sub_self]
  -- Could this be useful: adjMatrix_mulVec_const_apply?

lemma vec_adjMatrix_vec (x : V → ℤ) :
  x ⬝ᵥ mulVec (G.adjMatrix ℤ) x = ∑ i : V, ∑ j : V, if G.Adj i j then x i * x j else 0 := by
  unfold dotProduct mulVec
  unfold dotProduct
  simp [mul_sum]

lemma vec_degMatrix_vec (x : V → ℤ) :
  x ⬝ᵥ mulVec (G.degMatrix ℤ) x = ∑ i : V, G.degree i * x i * x i := by
  unfold dotProduct mulVec degMatrix dotProduct
  simp [mul_sum, mul_assoc, mul_comm]

lemma adj_sum_degree (i : V) : G.degree i = ∑ j : V, if G.Adj i j then 1 else 0 := by
  sorry

theorem vec_lapMatrix_vec (x : V → ℤ) :
  Matrix.toBilin' (G.lapMatrix ℤ) x x = ∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j)^2 else 0 := by -- How to sum over edges (i,j)?
  rw [Matrix.toBilin'_apply']
  unfold lapMatrix
  rw [sub_mulVec]
  simp only [dotProduct_sub]
  rw [vec_degMatrix_vec, vec_adjMatrix_vec]
  simp only [adj_sum_degree]
  sorry

/-Let x be in the kernel of L. For all vertices i,j whe have that if i and j
are connected, then x i = x j-/
lemma vngnsdiojf (x : V → ℤ) (h : Matrix.toBilin' (G.lapMatrix ℤ) x x = 0) :
  ∀i : V, ∀j : V, G.Adj i j → x i = x j := by
  intros i j
  by_contra hn
  have hc : Matrix.toBilin' (G.lapMatrix ℤ) x x ≠ 0
  {
    rw [vec_lapMatrix_vec]
    sorry
  }
  exact absurd h hc

/-Let x be in the kernel of L. For all vertices i,j whe have that if i and j
are reachable, then x i = x j-/
theorem no_name_yet (x : V → ℤ) (h : Matrix.toBilin' (G.lapMatrix ℤ) x x = 0):
  ∀i : V, ∀j : V, G.Reachable i j → x i = x j := by
  intros i j
  sorry


/-We now have that functions in the kernel of L are constant on connected components. Find a basis
of the kernel and show that it has size equal to the number of connected components-/


-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/FiniteDimensional.html
#check LinearMap.ker (Matrix.toLinearMap₂' (G.lapMatrix ℤ)) -- kernel
#check Module.rank ℤ (↥LinearMap.ker (Matrix.toLinearMap₂' (G.lapMatrix ℤ))) -- dimension of kernel
#check Fintype.card G.ConnectedComponent -- Number of connected components



-- This stuff down here probably won't ne needed anymore

-- The numbers of edges that are "cut" by removing a subset s of vertices
def cut : Finset V → ℕ :=
  fun s => ∑ i in s, ∑ j in sᶜ, (if G.Adj i j then 1 else 0)

variable (s : Finset V)

def cutIndicator : V → ℤ := fun i => if i ∈ s then 1 else -1

lemma cutIndicator_mul_cutIndicator (i j : V) :
  (cutIndicator s i) * (cutIndicator s j) =
  if ((i ∈ s ∧ j ∈ s) ∨ (i ∈ sᶜ ∧ j ∈ sᶜ)) then 1 else - 1 := by
  unfold cutIndicator
  split
  case inl h
  · simp [h]
  case inr h'
  · simp [h']

lemma cutIndicator_square (i : V) :
  (cutIndicator s i) * (cutIndicator s i) = 1 := by
  unfold cutIndicator
  split
  repeat simp

-- xᵀDx = ∑ᵢ dᵢ
lemma cutIndicator_degMatrix_cutIndicator :
  cutIndicator s ⬝ᵥ mulVec (G.degMatrix ℤ) (cutIndicator s) = ∑ i : V, G.degree i := by
  unfold mulVec dotProduct
  simp [Finset.mul_sum]
  unfold degMatrix
  simp [mul_comm, ← mul_assoc, cutIndicator_square]

-- xᵀDx = ∑₍ᵢⱼ₎ xᵢxⱼ
lemma cutIndicator_adjMatrix_cutIndicator :
  cutIndicator s ⬝ᵥ mulVec (G.adjMatrix ℤ) (cutIndicator s) =
  ∑ i : V, (∑ j : V, if G.Adj i j then (cutIndicator s i * cutIndicator s j) else 0) := by
  unfold mulVec dotProduct
  simp only [Finset.mul_sum]
  simp only [mul_comm, ← mul_assoc, cutIndicator_mul_cutIndicator]
  unfold adjMatrix
  simp

-- xᵀLx = 4*cut(S)
theorem cutIndicator_lapMatrix_cutIndicator_equals_four_cut :
  Matrix.toBilin' (G.lapMatrix ℤ) (cutIndicator s) (cutIndicator s) = 4*cut G s := by
  rw [Matrix.toBilin'_apply']
  unfold lapMatrix
  rw [sub_mulVec]
  simp only [dotProduct_sub]
  rw [cutIndicator_degMatrix_cutIndicator]
  rw [cutIndicator_adjMatrix_cutIndicator]
  sorry

-- If there is a vector in the kernel of L other than 1, we can construct a set with cut = 0
theorem vvkjre2 (y : V → ℤ) (h0 : y ≠ 0) (h_ker : mulVec (G.lapMatrix ℤ) y = 0)
  (h_ort : y ⬝ᵥ Function.const V 1 = 0) :
  ∃t : Finset V, Nonempty t ∧ cut G t = 0 := by
  use {i : V | y i > 0}.toFinset
  apply And.intro
  · simp
    sorry
  · sorry



/-
How to get all elements in the Fintype V, V.elems does not work
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Basic.html#Fintype.elems
-/
