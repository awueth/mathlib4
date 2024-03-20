import Mathlib.Combinatorics.SimpleGraph.LapMatrix

open BigOperators Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (α : Type*)

/-
def edge_boundary (s : Set V) : Set (SimpleGraph.edgeSet G) :=
  {(SimpleGraph.Dart.mk (u, v) h).edge | (u : V) (v : V) (h : G.Adj u v) (_ : u ∈ s) (_ : v ∉ s)}
-/

def cut (s : Finset V) : ℕ := ∑ u in s, ∑ v in sᶜ, (if G.Adj u v then 1 else 0)

theorem ite_or {α : Type u_1} [AddZeroClass α] (P Q : Prop) [Decidable P] [Decidable Q] (h : ¬(P ∧ Q)) (a : α) :
    (if P ∨ Q then a else 0) = (if P then a else 0) + if Q then a else 0 := by aesop

theorem cut_lapMatrix [Field α] [CharZero α] (s : Finset V) :
    cut G s = Set.indicator (↑s) 1 ⬝ᵥ G.lapMatrix α *ᵥ Set.indicator (↑s) 1 := by
  simp [← toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂', Set.indicator_apply]
  have h (u v : V) : ((if u ∈ s then (1 : α) else 0) - if v ∈ s then 1 else 0) ^ 2
      = (if (u ∈ s ∧ v ∉ s) ∨ (v ∈ s ∧ u ∉ s) then 1 else 0) := by aesop
  conv_rhs => arg 1; arg 2; intro u; arg 2; intro v; congr; rfl; rw [h]
  conv_rhs => arg 1; arg 2; intro u; arg 2; intro v; rw [← ite_and]; congr; rw [and_comm]
  conv_rhs => arg 1; arg 2; intro u; arg 2; intro v; rw [ite_and, ite_or]; rfl; tactic => simp; intro h1 _ _; exact h1
  conv_rhs => arg 1; arg 2; intro u; rw [sum_add_distrib]
  rw [sum_add_distrib]
  have h' : (∑ u : V, ∑ v : V, if u ∈ s ∧ v ∉ s then if G.Adj u v then 1 else 0 else 0) = ((cut G s) : α) := by
    simp only [ite_and, ite_not, sum_ite_irrel, sum_const_zero, sum_ite_mem, univ_inter]
    conv_lhs => arg 2; intro u; arg 2; intro v; rw [← ite_not]
    simp_rw [← mem_compl (s := s), sum_ite_mem, univ_inter, cut]
    simp
  have h'' : (∑ u : V, ∑ v : V, if v ∈ s ∧ u ∉ s then if G.Adj u v then 1 else 0 else 0) = ((cut G s) : α) := by
    rw [sum_comm]
    simp only [ite_and, ite_not, sum_ite_irrel, sum_const_zero, sum_ite_mem, univ_inter]
    conv_lhs => arg 2; intro u; arg 2; intro v; rw [← ite_not]
    simp_rw [← mem_compl (s := s), sum_ite_mem, univ_inter, SimpleGraph.adj_comm, cut]
    simp
  rw [h', h'']
  ring
