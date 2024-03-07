import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Function.Indicator
import Mathlib.Analysis.NormedSpace.Star.Matrix
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.InnerProductSpace.CourantFischer
import Mathlib.Data.FinEnum


open BigOperators Finset Matrix

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

section preliminaries

def volume (s : Finset V) : ℕ := ∑ v in s, G.degree v

/-
def edge_boundary (s : Set V) : Set (V × V) := {(u, v) | (u ∈ s) ∧ v ∉ s ∧ G.Adj u v}

def edge_boundary_v2 (s : Set V) : Set (SimpleGraph.edgeSet G) := Sym2.mk '' (edge_boundary G s)
-/

def cut (s : Finset V) : ℕ := ∑ u in s, ∑ v in sᶜ, (if G.Adj u v then 1 else 0)

noncomputable def conductance (s : Finset V) : ℝ := cut G s / min (volume G s) (volume G sᶜ)

theorem universe_powerSet_nonempty : (Finset.powerset (Finset.univ : Finset V)).Nonempty := by
  apply Finset.powerset_nonempty

noncomputable def minConductance : ℝ := (Finset.powerset (Finset.univ : Finset V)).inf'
  (universe_powerSet_nonempty) (conductance G)

noncomputable def eigenvalues_finset :
  Finset (Module.End.Eigenvalues (Matrix.toLin' G.normalLapMatrix)) := Finset.univ

noncomputable def eigenvalues_pos :=
  Set.toFinset {x : Module.End.Eigenvalues (Matrix.toLin' G.normalLapMatrix) | x > (0 : ℝ)}

noncomputable instance : LinearOrder (Module.End.Eigenvalues (toLin' G.normalLapMatrix)) := by
  rw [Module.End.Eigenvalues]
  infer_instance

/- Since G is connected, the kernel is one dimensional and there is a positive eigenvalue.
G being a nontrivial graph would suffice however. -/
noncomputable def gap (hc : G.Connected) : Module.End.Eigenvalues (Matrix.toLin' G.normalLapMatrix)
  := (eigenvalues_pos G).min' (sorry)

/- Why can the tuple be evaluated at -1? Why no proof of nonemptyness? -/
noncomputable def gap' : ℝ :=
  symm_matrix_eigenvalues_sorted G.normalLapMatrix G.isSymm_normalLapMatrix 1

def this_is_bad : Fin 3 := 7 -- why does this work?
def this_is_bad': Fin 3 := ⟨7, sorry⟩

#check this_is_bad.isLt
#check this_is_bad'.isLt

noncomputable def normalLapMatrixCLM := (Matrix.toEuclideanCLM (𝕜 := ℝ) G.normalLapMatrix)

end preliminaries

----------------------------------------------------------------------------------------------------

section easy_inequality

/- For a set s with minimal conductance, R(g) ≤ 2 h_G -/
noncomputable def g_low (s : Finset V) : WithLp 2 (V → ℝ) :=
  (Set.indicator s 1) - (fun _ => (volume G s : ℝ)/(volume G univ))

/- Orthogonal complement of D^(1/2) * 1 -/
noncomputable def sqrt_deg_perp :=
  (ℝ ∙ ((WithLp.equiv 2 _).symm <| ((Real.sqrt ∘ (G.degree ·)) * (fun _ ↦ 1 : V → ℝ))))ᗮ

/- λ = inf R(g) over g ⟂ D^(1/2) 1. Follows from Courant fischer. Uses the fact λ = λ₁ which
is true since G is connected. -/
theorem gap_eq_inf_rayleigh (hc : G.Connected) :
  gap G hc  = sInf (ContinuousLinearMap.rayleighQuotient (normalLapMatrixCLM G) '' (sqrt_deg_perp G)) := sorry

/- λ ≤ R(g) -/
theorem gap_le_rayleigh (s : Finset V) (hs : conductance G s = minConductance G) (hc : G.Connected) :
  gap G hc ≤ ContinuousLinearMap.rayleighQuotient (normalLapMatrixCLM G) (g_low G s) := by
  rw [gap_eq_inf_rayleigh]
  apply csInf_le
  · simp [BddBelow, Set.nonempty_def]
    use 0 -- 0 is a lower bound of the rayleigh quotient. Theorem for definite matrices?
    simp [lowerBounds]
    intro f hf
    sorry
  · apply Set.mem_image_of_mem
    simp [sqrt_deg_perp, Submodule.mem_orthogonal_singleton_iff_inner_right]
    sorry -- g ⟂ D^(1/2) 1

/- R(g) ≤ 2 * h -/
theorem rayleigh_le_minConductance (s : Finset V) (hs : conductance G s = minConductance G) :
  ContinuousLinearMap.rayleighQuotient (normalLapMatrixCLM G) (g_low G s) ≤ 2 * (minConductance G) := by
  simp [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf]
  sorry

theorem cheeger_ineq_easy (hc : G.Connected) : gap G hc ≤ 2 * (minConductance G) := by
  obtain ⟨s, _, h⟩ := Finset.exists_mem_eq_inf' universe_powerSet_nonempty (conductance G)
  rw [← minConductance] at h
  apply LE.le.trans (gap_le_rayleigh G s (Eq.symm h) hc) (rayleigh_le_minConductance G s (Eq.symm h))

end easy_inequality

----------------------------------------------------------------------------------------------------

section hard_inequality

variable [FinEnum V]

def vertex_tuple : Fin (FinEnum.card V) → V := (@FinEnum.equiv V).invFun

noncomputable def vertex_tuple_sorted (f : V → ℝ) : Fin (FinEnum.card V) → V :=
  vertex_tuple ∘ Tuple.sort (f ∘ vertex_tuple)

noncomputable def sweep (f : V → ℝ) (i : Fin (FinEnum.card V)) :=
  ((vertex_tuple_sorted f) '' {j : Fin (FinEnum.card V) | j < i}).toFinset

noncomputable def min_sweep_conductance (f : V → ℝ) :=
  {sweep f i | i : Fin (FinEnum.card V)}.toFinset.inf' (sorry) (conductance G)

/- h_G ≤ α_G -/
theorem my_ineq1 (f : V → ℝ) : minConductance G ≤ (min_sweep_conductance G f) := by
  simp [minConductance, min_sweep_conductance]
  intro s _
  use s

/- α² / 2 ≤ λ, long chain of inequalities -/
theorem my_ineq2 (f : V → ℝ) (hc : G.Connected)
  (hf : Module.End.HasEigenvector (Matrix.toLin' G.normalLapMatrix) (gap G hc) f) :
  (min_sweep_conductance G f)^2 / 2 ≤ gap G hc := sorry

/- h_G²/2 ≤ α²/2 ≤ λ -/
theorem cheeger_ineq_hard (hc : G.Connected) : minConductance G^2 / 2 ≤ gap G hc := by
  obtain ⟨f, hf⟩ := Module.End.HasEigenvalue.exists_hasEigenvector (gap G hc).2
  have h : minConductance G^2 / 2 ≤ (min_sweep_conductance G f)^2 / 2 := by
    ring_nf
    simp
    apply sq_le_sq'
    · apply sub_nonneg.1
      rw [sub_neg_eq_add]
      apply add_nonneg
      · sorry -- 0 ≤ min_conductance G. Define conductance as NNReal?
      · sorry -- 0 ≤ min_sweep_conductance G f
    · exact my_ineq1 G f
  calc
    minConductance G^2 / 2 ≤ (min_sweep_conductance G f)^2 / 2 := h
    (min_sweep_conductance G f)^2 / 2 ≤ gap G hc := by exact my_ineq2 G f hc hf
