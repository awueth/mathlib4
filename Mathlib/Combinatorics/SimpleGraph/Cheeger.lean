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

theorem R_pos (f : V → ℝ) : 0 ≤ R G f := by
  unfold R
  apply div_nonneg
  · apply sum_nonneg
    intro _ _
    simp [sq_nonneg]
  · apply mul_nonneg (zero_le_two);
    apply sum_nonneg
    intro _ _
    apply mul_nonneg
    · apply sq_nonneg
    · apply Nat.cast_nonneg

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


noncomputable def gLow (s : Finset V) : V → ℝ :=
  (volume G univ : V → ℝ) * (Set.indicator s 1) - (volume G s : V → ℝ)

theorem sum_gLow_mul_degree (s : Finset V) : ∑ v : V, gLow G s v * G.degree v = 0 := by
  simp only [gLow, Pi.natCast_def, Pi.sub_apply, Pi.mul_apply, sub_mul, sum_sub_distrib]
  simp_rw [mul_assoc ((volume G univ) : ℝ) (s.toSet.indicator 1 ?x) ((G.degree ?x) : ℝ), ← mul_sum]
  apply sub_eq_zero.2
  simp only [Set.indicator_apply, mem_coe, Pi.one_apply, ite_mul, one_mul, zero_mul, sum_ite_mem,
    univ_inter, ← Nat.cast_sum]
  rw [← volume, ← volume, mul_comm]

theorem one (s : Finset V) :
    ∑ (u : V) (v : V) with G.Adj u v, (gLow G s u - gLow G s v) ^ 2 = 2 * (volume G univ : ℝ) ^ 2 * cut G s := by
  simp only [univ_product_univ, gLow, Pi.natCast_def, Pi.sub_apply, Pi.mul_apply,
    sub_sub_sub_cancel_right]
  conv_lhs => arg 2; intro x; rw [← mul_sub, mul_pow]
  rw [← mul_sum]
  simp [Set.indicator_apply]
  have h (u v : V) : ((if u ∈ s then (1 : ℝ) else 0) - if v ∈ s then 1 else 0) ^ 2
      = (if (u ∈ s ∧ v ∉ s) ∨ (v ∈ s ∧ u ∉ s) then 1 else 0) := by aesop
  conv_lhs => arg 2; arg 2; intro x; rw [h, ite_or]; rfl; tactic => aesop
  rw [sum_add_distrib]
  sorry

theorem two (s : Finset V) :
    ∑ v, (gLow G s v) ^ (2 : ℕ) * G.degree v = (volume G univ) * (volume G s) * (volume G sᶜ) := by
  simp only [gLow, Pi.natCast_def, Pi.sub_apply, Pi.mul_apply, Set.indicator_apply, mem_coe,
    Pi.one_apply, mul_ite, mul_one, mul_zero]
  simp [sub_sq', sub_mul, add_mul, sum_sub_distrib, sum_add_distrib]
  sorry

theorem three (s : Finset V) : R G (gLow G s) ≤  2 * (conductance G s : ℝ) := by
  rw [R, one G s, two G s]
  calc
    2 * ↑(volume G univ) ^ 2 * ↑(cut G s) / (2 * (↑(volume G univ) * ↑(volume G s) * ↑(volume G sᶜ)))
      = (volume G univ : ℝ) * ↑(cut G s) / (↑(volume G s) * ↑(volume G sᶜ)) := sorry
    _ = ↑(volume G univ) * ↑(cut G s) / (max (volume G s) (volume G sᶜ) * min (volume G s) (volume G sᶜ)) := by simp only [Nat.cast_max, Nat.cast_min, max_mul_min]
    _ ≤ ↑(2 * max (volume G s) (volume G sᶜ)) * ↑(cut G s) / (max (volume G s) (volume G sᶜ) * min (volume G s) (volume G sᶜ)) := by gcongr; exact volume_univ_le_max G s
    _ = 2 * ((cut G s) /  min (volume G s) (volume G sᶜ)) := sorry
    _ = 2 * conductance G s := by simp [conductance];

#check max_mul_min

theorem four : gap G ≤ 2 * (minConductance G : ℝ) := by
  obtain ⟨s, _, h⟩ := Finset.exists_mem_eq_inf' universe_powerSet_nonempty (conductance G)

  have hBdd : BddBelow (Set.range fun f : {f : V → ℝ // ∑ v, f v * G.degree v = 0} ↦ R G ↑f) := by
    simp only [BddBelow, Set.nonempty_def]
    use 0;
    simp only [lowerBounds, Set.mem_range, Subtype.exists, exists_prop, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂, Set.mem_setOf_eq]
    intro f _
    exact R_pos G f
  have hmem :
      R G (gLow G s) ∈ (Set.range fun f : {f : V → ℝ // ∑ v, f v * G.degree v = 0} ↦ R G ↑f) := by
    simp only [Set.mem_range, Subtype.exists, exists_prop]
    use gLow G s
    constructor
    · exact sum_gLow_mul_degree G s
    · rfl

  unfold gap
  calc
    gap G ≤ R G (gLow G s) := by rw [gap]; apply csInf_le hBdd hmem;
    _ ≤ 2 * (conductance G s) := by simp_rw [three G s]
    _ = 2 * (minConductance G : ℝ) := by rw [minConductance, h]
