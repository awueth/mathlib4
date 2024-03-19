import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Function.Indicator
import Mathlib.Analysis.NormedSpace.Star.Matrix
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.InnerProductSpace.CourantFischer
import Mathlib.Data.FinEnum
import Mathlib.Data.Matrix.Basic


open BigOperators Finset Matrix

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (hV : 1 < Fintype.card V )
variable (G : SimpleGraph V) [DecidableRel G.Adj] (hd : ∀ v : V, 0 < G.degree v)

section preliminaries

def volume (s : Finset V) : ℕ := ∑ v in s, G.degree v

/-
def edge_boundary (s : Set V) : Set (V × V) := {(u, v) | (u ∈ s) ∧ v ∉ s ∧ G.Adj u v}

def edge_boundary_v2 (s : Set V) : Set (SimpleGraph.edgeSet G) := Sym2.mk '' (edge_boundary G s)
-/

def cut (s : Finset V) : ℕ := ∑ u in s, ∑ v in sᶜ, (if G.Adj u v then 1 else 0)

noncomputable def conductance (s : Finset V) : NNReal := cut G s / min (volume G s) (volume G sᶜ)

theorem universe_powerSet_nonempty : (Finset.powerset (Finset.univ : Finset V)).Nonempty := by
  apply Finset.powerset_nonempty

noncomputable def minConductance : NNReal := (Finset.powerset (Finset.univ : Finset V)).inf'
  (universe_powerSet_nonempty) (conductance G)

noncomputable def eigenvalues_finset :
  Finset (Module.End.Eigenvalues (Matrix.toLin' G.normalLapMatrix)) := Finset.univ

noncomputable def eigenvalues_pos :=
  Set.toFinset {x : Module.End.Eigenvalues (Matrix.toLin' G.normalLapMatrix) | x > (0 : ℝ)}

noncomputable instance : LinearOrder (Module.End.Eigenvalues (toLin' G.normalLapMatrix)) := by
  rw [Module.End.Eigenvalues]
  infer_instance

/-
theorem eigenvalues_pos_Nonempty : (eigenvalues_pos G).Nonempty := by
  simp [Finset.Nonempty, eigenvalues_pos]
  simp only [Module.End.Eigenvalues._eq_1]
  obtain ⟨v, t, ht, hv, h⟩ := Matrix.IsHermitian.exists_eigenvector_of_ne_zero (A := G.normalLapMatrix) (G.isSymm_normalLapMatrix) (sorry)
  use ⟨t, sorry⟩
  sorry
-/

/- Since G is connected, the kernel is one dimensional and there is a positive eigenvalue.
G being a nontrivial graph would suffice however.
noncomputable def gap (hc : G.Connected) : Module.End.Eigenvalues (Matrix.toLin' G.normalLapMatrix)
  := (eigenvalues_pos G).min' (sorry)
-/

/- Why can the tuple be evaluated at -1? Why no proof of nonemptyness? -/
noncomputable def gap : ℝ :=
  symm_matrix_eigenvalues_sorted G.isSymm_normalLapMatrix ⟨1, hV⟩

theorem gap_is_eig :
    Module.End.HasEigenvalue (Matrix.toLin' G.normalLapMatrix) (gap hV G) := by
  rw [gap]
  apply (symm_matrix_eigenvalues_sorted_is_eig G.isSymm_normalLapMatrix ⟨1, _⟩)

noncomputable def normalLapMatrixCLM := (Matrix.toEuclideanCLM (𝕜 := ℝ) G.normalLapMatrix)

end preliminaries

----------------------------------------------------------------------------------------------------

theorem matrixReApplyInnerSelf (A : Matrix V V ℝ) (x : WithLp 2 (V → ℝ)) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).reApplyInnerSelf x =
    x ⬝ᵥ A *ᵥ x := by
  rw [ContinuousLinearMap.reApplyInnerSelf, EuclideanSpace.inner_eq_star_dotProduct,
    piLp_equiv_toEuclideanCLM, toLin'_apply, star_trivial, IsROrC.re_to_real, dotProduct_comm]
  rfl


theorem matrixRayleighQuotient (A : Matrix V V ℝ) (x : WithLp 2 (V → ℝ)) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient x =
    x ⬝ᵥ A *ᵥ x / ∑ i : V, x i ^ 2 := by
  simp_rw [ContinuousLinearMap.rayleighQuotient, matrixReApplyInnerSelf, PiLp.norm_sq_eq_of_L2,
    Real.norm_eq_abs, sq_abs]

theorem matrixreApplyInnerSelf' (A : Matrix V V ℝ) (x : V → ℝ) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).reApplyInnerSelf ((WithLp.equiv 2 (V → ℝ)).symm x) =
    x ⬝ᵥ A *ᵥ x := by
  rw [matrixReApplyInnerSelf]
  rfl

theorem matrixRayleighQuotient' (A : Matrix V V ℝ) (x : V → ℝ) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient ((WithLp.equiv 2 (V → ℝ)).symm x) =
    x ⬝ᵥ A *ᵥ x / ∑ i : V, x i ^ 2 := by
  rw [matrixRayleighQuotient]
  rfl
/-
theorem xLx (x : V → ℝ) : x ⬝ᵥ G.normalLapMatrix *ᵥ x = (∑ i : V, ∑ j : V,
    if G.Adj i j then (x i / Real.sqrt (G.degree i) - x j / Real.sqrt (G.degree j))^2 else 0) / 2 := by
  rw [SimpleGraph.normalLapMatrix]
  sorry
-/

theorem dotProduct_mulVec_normalLapMatrix (x : V → ℝ) : x ⬝ᵥ G.normalLapMatrix  *ᵥ x
    = ((diagonal (Real.sqrt ∘ (G.degree ·)))⁻¹ *ᵥ x) ⬝ᵥ G.lapMatrix ℝ *ᵥ ((diagonal (Real.sqrt ∘ (G.degree ·)))⁻¹ *ᵥ x) := by
  rw [SimpleGraph.normalLapMatrix, mul_assoc, mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    ← mulVec_transpose, transpose_nonsing_inv, diagonal_transpose]

theorem dotProduct_mulVec_lapMatrix (x : V → ℝ) : (diagonal (Real.sqrt ∘ (G.degree ·)) *ᵥ x) ⬝ᵥ G.normalLapMatrix  *ᵥ (diagonal (Real.sqrt ∘ (G.degree ·)) *ᵥ x)
    = x ⬝ᵥ G.lapMatrix ℝ *ᵥ x := by
  rw [dotProduct_mulVec_normalLapMatrix, mulVec_mulVec, Matrix.nonsing_inv_mul, one_mulVec]
  simp only [IsUnit, det_diagonal, Function.comp_apply, Units.exists_iff_ne_zero]
  refine prod_ne_zero_iff.mpr ?h.a
  intro v _
  simp only [ne_eq, Nat.cast_nonneg, Real.sqrt_eq_zero, Nat.cast_eq_zero]
  exact Nat.pos_iff_ne_zero.mp (hd v)

----------------------------------------------------------------------------------------------------

section easy_inequality

noncomputable def g_aux (s : Finset V) : V → ℝ :=
  (volume G univ : V → ℝ) * (Set.indicator s 1) - (volume G s : V → ℝ)

noncomputable def D_sqrt :=  diagonal (Real.sqrt ∘ (G.degree ·))

/- For a set s with minimal conductance, R(g) ≤ 2 h_G -/
noncomputable def g_low (s : Finset V) : WithLp 2 (V → ℝ) := (WithLp.equiv 2 (V → ℝ)).symm <|
  D_sqrt G *ᵥ (g_aux G s)

theorem g_low_apply (s : Finset V) (v : V) : g_low G s v =
    (if v ∈ s then Real.sqrt (G.degree v) * (volume G univ : ℝ) else 0) - (Real.sqrt (G.degree v) * (volume G s : ℝ)) := by
  simp [g_low, g_aux, D_sqrt, Pi.coe_nat, WithLp.equiv_symm_pi_apply, mulVec, dotProduct_sub,
    diagonal_dotProduct, Function.comp_apply, Pi.mul_apply, Set.indicator_apply, mem_coe,
    Pi.one_apply, mul_ite, mul_one, mul_zero]

/- g_low ⟂ D^(1/2) 1 -/
theorem g_low_orthogonal (s : Finset V) :
    ⟪(WithLp.equiv 2 (V → ℝ)).symm <| fun v ↦ Real.sqrt (G.degree v), g_low G s⟫_ℝ = 0 := by
  simp [g_low_apply, finsum_congr, mul_sub, ← mul_assoc, ← sum_mul, volume, mul_comm]


/- Orthogonal complement of D^(1/2) * 1 -/
noncomputable def sqrt_deg_perp :=
  (ℝ ∙ ((WithLp.equiv 2 (V → ℝ)).symm <| fun v ↦ Real.sqrt (G.degree v)))ᗮ

/- λ = inf R(g) over g ⟂ D^(1/2) 1. Follows from Courant fischer. Uses the fact λ = λ₁ which
is true since G is connected. -/
theorem gap_eq_inf_rayleigh :
    gap hV G  = sInf ((normalLapMatrixCLM G).rayleighQuotient '' (sqrt_deg_perp G)) := by
  rw [sInf_image']
  apply le_antisymm
  · sorry
  · sorry

/- λ ≤ R(g) -/
theorem gap_le_rayleigh (s : Finset V) (hs : conductance G s = minConductance G) :
  gap hV G ≤ (normalLapMatrixCLM G).rayleighQuotient (g_low G s) := by
  rw [gap_eq_inf_rayleigh hV G]
  apply csInf_le
  · simp [BddBelow, Set.nonempty_def]
    use 0 -- 0 is a lower bound of the rayleigh quotient. Theorem for definite matrices?
    simp [lowerBounds]
    intro f _
    rw [normalLapMatrixCLM, ContinuousLinearMap.rayleighQuotient, matrixReApplyInnerSelf]
    apply div_nonneg
    · apply Matrix.PosSemidef.re_dotProduct_nonneg (𝕜 := ℝ) G.posSemidef_normalLapMatrix f
    · apply sq_nonneg
  · apply Set.mem_image_of_mem -- g ⟂ D^(1/2) 1
    rw [sqrt_deg_perp, SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, g_low_orthogonal]

example : ((volume G univ) : ℝ) / ↑(volume G univ) ≤ 1 := by apply div_self_le_one

/- R(g) ≤ 2 * h -/ -- Remember this theorem: max_mul_min
theorem rayleigh_le_minConductance (s : Finset V) (hs : conductance G s = minConductance G) :
    (normalLapMatrixCLM G).rayleighQuotient (g_low G s) ≤ 2 * (minConductance G) := by
  rw [normalLapMatrixCLM, g_low, matrixRayleighQuotient']
  have h1 : D_sqrt G *ᵥ g_aux G s ⬝ᵥ SimpleGraph.normalLapMatrix G *ᵥ D_sqrt G *ᵥ g_aux G s =
      cut G s * (volume G univ)^2 := by
    rw [D_sqrt, dotProduct_mulVec_lapMatrix G hd, g_aux]
    set L := G.lapMatrix ℝ
    rw [mulVec_sub, sub_dotProduct]
    sorry
  have h2 : ∑ i : V, (D_sqrt G *ᵥ g_aux G s) i ^ (2 : ℕ) =
      (volume G univ) * (volume G s) * (volume G sᶜ) := by
    simp [D_sqrt, mulVec_diagonal, mul_pow, g_aux, sub_sq]
    have hi : (v : V) → (Set.indicator s (1 : V → ℝ) v ^ 2 = Set.indicator s (1 : V → ℝ) v) := by
      simp [sq, Set.indicator_apply]
    simp [hi]
    set d := G.degree with hd
    set χ := Set.indicator s (1 : V → ℝ) with hχ
    set VG := volume G univ with hVG
    set VS := volume G s with hVS
    set VSC := volume G sᶜ with hVSC
    calc
      _ = ∑ x : V, ↑(d x) * ((↑VG ^ 2 - 2 * ↑VG * ↑VS) * χ x + ↑VS ^ 2) := by sorry
      _ = ∑ x : V, (↑(d x) * (↑VG ^ 2 - 2 * ↑VG * ↑VS) * χ x + ↑(d x) * ↑VS ^ 2) := by sorry
      _ = ∑ x : V, ↑(d x) * (↑VG ^ 2 - 2 * ↑VG * ↑VS) * χ x + ∑ x : V, ↑(d x) * ↑VS ^ 2 := by sorry
      _ = (∑ x : s, ↑(d x)) * (↑VG ^ 2 - 2 * ↑VG * ↑VS) + (∑ x : V, ↑(d x)) * ↑VS ^ 2 := by sorry
      _ = ↑VG * ↑VS * (↑VG - ↑VS) := by sorry
      _ = ↑VG * ↑VS * ↑VSC := sorry
  rw [h1, h2]
  have h3 : ((volume G univ) : ℝ) / ↑(volume G univ) ≤ 1 := by apply div_self_le_one
  calc
    _ = ↑(cut G s) * ↑(volume G univ) * (↑(volume G univ) / ↑(volume G univ)) / (↑(volume G s) * ↑(volume G sᶜ)) := by ring
    _ ≤ ↑(cut G s) * ↑(volume G univ) * (1 : ℝ) / (↑(volume G s) * ↑(volume G sᶜ)) := by sorry -- simp [div_self_le_one ((volume G univ) : ℝ)]
    _ = ↑(cut G s) * ↑(volume G univ) / (↑(volume G s) * ↑(volume G sᶜ)) := by simp only [mul_one]
    _ ≤ ↑(cut G s) * ↑(volume G univ) / (max ↑(volume G s) ↑(volume G sᶜ) * min ↑(volume G s) ↑(volume G sᶜ)) := by rw [max_mul_min]
    _ = ↑(cut G s) * (↑(volume G univ) / max ↑(volume G s) ↑(volume G sᶜ)) / (min ↑(volume G s) ↑(volume G sᶜ)) := by ring
    _ ≤ ↑(cut G s) * (2 * max ↑(volume G s) ↑(volume G sᶜ) / max ↑(volume G s) ↑(volume G sᶜ)) / (min ↑(volume G s) ↑(volume G sᶜ)) := by sorry
    _ ≤ ↑(cut G s) * 2 / (min ↑(volume G s) ↑(volume G sᶜ)) := by sorry
    _ = 2 * (↑(cut G s) / (min ↑(volume G s) ↑(volume G sᶜ))) := by ring
    _ = 2 * (conductance G s) := by simp [conductance]
    _ ≤ 2 * (minConductance G) := by rw [hs];


theorem cheeger_ineq_easy : gap hV G ≤ 2 * (minConductance G : ℝ) := by
    obtain ⟨s, _, h⟩ := Finset.exists_mem_eq_inf' universe_powerSet_nonempty (conductance G)
    rw [← minConductance] at h
    apply LE.le.trans (gap_le_rayleigh hV G s (Eq.symm h)) (rayleigh_le_minConductance G s (Eq.symm h))

end easy_inequality

----------------------------------------------------------------------------------------------------

section hard_inequality

variable [FinEnum V]

def vertex_tuple : Fin (FinEnum.card V) → V := (@FinEnum.equiv V).invFun

noncomputable def vertex_tuple_sorted (f : V → ℝ) : Fin (FinEnum.card V) → V :=
  vertex_tuple ∘ Tuple.sort (f ∘ vertex_tuple)

noncomputable def sweep (f : V → ℝ) (i : Fin (FinEnum.card V)) :=
  ((vertex_tuple_sorted f) '' {j : Fin (FinEnum.card V) | j < i}).toFinset

noncomputable def min_sweep_conductance (f : V → ℝ) : NNReal :=
  {sweep f i | i : Fin (FinEnum.card V)}.toFinset.inf' (sorry) (conductance G)

/- h_G ≤ α_G -/
theorem my_ineq1 (f : V → ℝ) : minConductance G ≤ (min_sweep_conductance G f) := by
  simp [minConductance, min_sweep_conductance]
  intro s _
  use s

/- α² / 2 ≤ λ, long chain of inequalities -/
theorem my_ineq2 {f : V → ℝ}
  (hf : Module.End.HasEigenvector (Matrix.toLin' G.normalLapMatrix) (gap hV G) f) :
  (min_sweep_conductance G f : ℝ)^2 / 2 ≤ gap hV G := sorry

/- h_G²/2 ≤ α²/2 ≤ λ -/
theorem cheeger_ineq_hard : (minConductance G : ℝ)^2 / 2 ≤ gap hV G := by
  obtain ⟨f, hf⟩ := Module.End.HasEigenvalue.exists_hasEigenvector (gap_is_eig hV G) --(gap G hc).2
  have h : minConductance G^2 / 2 ≤ (min_sweep_conductance G f)^2 / 2 := by
    simp [NNReal.le_div_iff_mul_le]
    rw [← NNReal.coe_le_coe]
    apply sq_le_sq' -- Theorem for NNReal?
    · apply sub_nonneg.1
      rw [sub_neg_eq_add]
      apply add_nonneg
      · simp only [NNReal.val_eq_coe, NNReal.zero_le_coe]
      · simp only [NNReal.val_eq_coe, NNReal.zero_le_coe]
    · exact my_ineq1 G f
  calc
    (minConductance G)^2 / 2 ≤ (min_sweep_conductance G f : ℝ)^2 / 2 := h
    _ ≤ ↑(gap hV G) := by exact my_ineq2 hV G hf
