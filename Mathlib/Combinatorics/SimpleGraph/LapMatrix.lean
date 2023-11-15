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
import Mathlib.LinearAlgebra.Finrank

open BigOperators Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq G.ConnectedComponent]

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

lemma vec_adjMatrix_vec (x : V → ℝ) :
  x ⬝ᵥ mulVec (G.adjMatrix ℝ) x = ∑ i : V, ∑ j : V, if G.Adj i j then x i * x j else 0 := by
  unfold dotProduct mulVec
  unfold dotProduct
  simp [mul_sum]

lemma vec_degMatrix_vec (x : V → ℝ) :
  x ⬝ᵥ mulVec (G.degMatrix ℝ) x = ∑ i : V, G.degree i * x i * x i := by
  unfold dotProduct mulVec degMatrix dotProduct
  simp [mul_sum, mul_assoc, mul_comm]

lemma sum_adj_eq_degree (i : V) : (G.degree i : ℝ) = ∑ j : V, if G.Adj i j then 1 else 0 := by
  have h : (∑ j : V, if G.Adj i j then 1 else 0) = (G.adjMatrix ℝ).mulVec (Function.const V 1) i
  · unfold mulVec dotProduct
    simp only [sum_boole, mem_univ, forall_true_left, adjMatrix_apply, Function.const_apply, mul_one]
  rw [h]
  simp [degree]

lemma ite_sub_distr (P : Prop) [Decidable P] (a b : ℝ) : ((if P then a else 0) - if P then b else 0) =
  if P then a - b else 0 := by
  split
  rfl
  rw [sub_self]

lemma ite_add_distr (P : Prop) [Decidable P] (a b : ℝ) : ((if P then a else 0) + if P then b else 0) =
  if P then a + b else 0 := by
  split
  rfl
  rw [add_zero]

lemma massage (f : V → ℝ) : ∑ i : V, f i = (∑ i : V, f i + ∑ i : V, f i) / 2 := by
  rw [half_add_self]

lemma switcheroo (x : V → ℝ) : (∑ i : V, ∑ x_1 : V, if Adj G i x_1 then x i * x i - x i * x x_1 else 0)
  = (∑ i : V, ∑ x_1 : V, if Adj G i x_1 then x x_1 * x x_1 - x x_1 * x i else 0) := by
  sorry

theorem vec_lapMatrix_vec (x : V → ℝ) :
  Matrix.toBilin' (G.lapMatrix ℝ) x x = (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j)^2 else 0) / 2 := by
  rw [Matrix.toBilin'_apply']
  unfold lapMatrix
  rw [sub_mulVec]
  simp only [dotProduct_sub]
  rw [vec_degMatrix_vec, vec_adjMatrix_vec, ← sum_sub_distrib]
  simp only [sum_adj_eq_degree, sum_mul, ← sum_sub_distrib, ite_mul, one_mul, zero_mul, ite_sub_distr]
  rw [massage]
  conv => lhs; arg 1; arg 2; rw [switcheroo]
  simp [← sum_add_distrib]
  conv => lhs; arg 1; arg 2; intro i; arg 2; intro j; rw [ite_add_distr]
  field_simp
  rw [sum_congr]
  rfl
  intros i _
  rw [sum_congr]
  rfl
  intros j _
  split
  rw [pow_two]
  ring
  rfl


/-Let x be in the kernel of L. For all vertices i,j whe have that if i and j
are adjacent, then x i = x j-/
lemma ker_adj_eq (x : V → ℝ) (h : Matrix.toBilin' (G.lapMatrix ℝ) x x = 0) :
  ∀i : V, ∀j : V, G.Adj i j → x i = x j := by
  intros i j
  by_contra hn
  have hc : Matrix.toBilin' (G.lapMatrix ℝ) x x ≠ 0
  · rw [vec_lapMatrix_vec]
    sorry
  exact absurd h hc

/-Let x be in the kernel of L. For all vertices i,j whe have that if i and j
are reachable, then x i = x j-/
theorem ker_reachable_eq (x : V → ℝ) (h : Matrix.toBilin' (G.lapMatrix ℝ) x x = 0) :
  ∀i : V, ∀j : V, G.Reachable i j → x i = x j := by
  intros i j
  unfold Reachable
  sorry

/-We now have that functions in the kernel of L are constant on connected components. Find a basis
of the kernel and show that it has size equal to the number of connected components-/

/-Given a connected component, return the vector which is one on all vertices of the component
and zero elsewhere-/
def myBasis (c : G.ConnectedComponent) : LinearMap.ker (Matrix.toLinearMap₂' (G.lapMatrix ℝ)) :=
  ⟨fun i ↦ if G.connectedComponentMk i = c then 1 else 0, sorry⟩

lemma myBasis_linearIndependent :
  LinearIndependent ℝ (myBasis G) := by
  rw [Fintype.linearIndependent_iff]
  intro g
  unfold myBasis
  simp
  conv =>
    lhs
    lhs
    arg 2
    intro c
    arg 1
    -- ????
  sorry


lemma myBasis_spanning :
  ⊤ ≤ Submodule.span ℝ (Set.range (myBasis G)) := by
  sorry

theorem rank_ker_lapMatrix_eq_card_ConnectedComponent : Fintype.card G.ConnectedComponent =
  FiniteDimensional.finrank ℝ (LinearMap.ker (Matrix.toLinearMap₂' (G.lapMatrix ℝ))) := by
  rw [FiniteDimensional.finrank_eq_card_basis (Basis.mk (myBasis_linearIndependent G) (myBasis_spanning G))]

-- This stuff down here probably won't ne needed anymore
/-
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
-/
