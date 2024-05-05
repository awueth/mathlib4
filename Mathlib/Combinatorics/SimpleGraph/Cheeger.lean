import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Cut
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Function.Indicator
import Mathlib.Analysis.NormedSpace.Star.Matrix
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.FinEnum
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Group.PosPart



open BigOperators Finset Matrix


variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (hV : 1 < Fintype.card V )
variable (G : SimpleGraph V) [DecidableRel G.Adj] (hd : ∀ v : V, 0 < G.degree v)


section preliminaries

noncomputable abbrev R (f : V → ℝ) : ℝ := (∑ (u : V) (v : V) with G.Adj u v, (f u - f v) ^ 2) / (2 * ∑ v, f v^2 * G.degree v)

noncomputable def gap : ℝ :=
  ⨅ f : {f : V → ℝ // ∑ v, f v * G.degree v = 0}, R G f

def volume (s : Finset V) : ℕ := ∑ v in s, G.degree v

theorem volume_univ (s : Finset V) : volume G univ = volume G s + volume G sᶜ := by
  unfold volume
  rw [← sum_add_sum_compl s]

theorem volume_compl (s : Finset V) : volume G sᶜ = volume G univ - volume G s := by
  rw [volume_univ G s, add_tsub_cancel_left]

theorem volume_monotone {s t : Finset V} (h : s ⊆ t) : volume G s ≤ volume G t := by
  unfold volume
  exact sum_le_sum_of_subset h

theorem volume_univ_le_max (s : Finset V) : volume G univ ≤ 2 * max (volume G s) (volume G sᶜ) := by
    cases max_cases (volume G s) (volume G sᶜ) with
    | inl h₁ => rw [h₁.1, volume_univ G s, two_mul]; rel [h₁.2]
    | inr h₂ => rw [h₂.1, volume_univ G s, two_mul]; rel [h₂.2]

noncomputable def conductance (s : Finset V) : NNReal := cut G s / min (volume G s) (volume G sᶜ)

theorem universe_powerSet_nonempty : (Finset.powerset (Finset.univ : Finset V)).Nonempty := by
  apply Finset.powerset_nonempty

noncomputable def minConductance : NNReal := (Finset.powerset (Finset.univ : Finset V)).inf'
  (universe_powerSet_nonempty) (conductance G)

end preliminaries


noncomputable def g_low (s : Finset V) : V → ℝ :=
  (volume G univ : V → ℝ) * (Set.indicator s 1) - (volume G s : V → ℝ)

theorem one (s : Finset V) :
    ∑ (u : V) (v : V) with G.Adj u v, (g_low G s u - g_low G s v) ^ 2 = (volume G univ : ℝ) ^ 2 * cut G s := by
  simp [g_low]
  conv_lhs => arg 2; intro x; rw [← mul_sub, mul_pow]
  rw [← mul_sum]
  congr
  sorry

theorem two (s : Finset V) :
    ∑ v, (g_low G s v) ^ (2 : ℕ) * G.degree v = (volume G univ) * (volume G s) * (volume G sᶜ) := by
  simp [g_low, Set.indicator_apply]
  sorry

theorem three (s : Finset V) : R G (g_low G s) ≤  2 * (conductance G s) := by
  rw [R, one G s, two G s]
  sorry

theorem four : gap G ≤ 2 * (minConductance G : ℝ) := by
  obtain ⟨s, _, h⟩ := Finset.exists_mem_eq_inf' universe_powerSet_nonempty (conductance G)
  unfold gap
  calc
    gap G ≤ R G (g_low G s) := sorry
    _ ≤ 2 * (conductance G s) := by simp_rw [three G s]
    _ = 2 * (minConductance G : ℝ) := by rw [minConductance, h]
