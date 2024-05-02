import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Cut
import Mathlib.Combinatorics.SimpleGraph.CheegerUtils
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

noncomputable instance sqrt_degree_invertible :
    Invertible (diagonal (Real.sqrt ∘ fun x ↦ ↑(G.degree x))) := by
  refine invertibleOfIsUnitDet (diagonal (Real.sqrt ∘ fun x ↦ ↑(SimpleGraph.degree G x))) ?h
  simp only [IsUnit, det_diagonal, Function.comp_apply, Units.exists_iff_ne_zero]
  refine prod_ne_zero_iff.mpr ?h.a
  intro v _
  simp only [ne_eq, Nat.cast_nonneg, Real.sqrt_eq_zero, Nat.cast_eq_zero]
  exact Nat.pos_iff_ne_zero.mp (hd v)

section preliminaries

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

-- noncomputable def minConductance' : NNReal := ⨅ s : Finset V, conductance G s

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
    piLp_equiv_toEuclideanCLM, toLin'_apply, star_trivial, RCLike.re_to_real, dotProduct_comm]
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
  haveI : Invertible (diagonal (Real.sqrt ∘ (G.degree ·))) := sqrt_degree_invertible G hd
  rw [dotProduct_mulVec_normalLapMatrix, mulVec_mulVec, inv_mul_of_invertible, one_mulVec]

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
  simp [g_low, g_aux, D_sqrt, Pi.natCast_def, WithLp.equiv_symm_pi_apply, mulVec, dotProduct_sub,
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
theorem gap_le_rayleigh (s : Finset V):
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

/- R(g) ≤ 2 * h -/ -- Remember this theorem: max_mul_min
theorem rayleigh_le_minConductance (s : Finset V) (hs : conductance G s = minConductance G) :
    (normalLapMatrixCLM G).rayleighQuotient (g_low G s) ≤ 2 * (minConductance G) := by
  rw [normalLapMatrixCLM, g_low, matrixRayleighQuotient']
  have h1 : D_sqrt G *ᵥ g_aux G s ⬝ᵥ SimpleGraph.normalLapMatrix G *ᵥ D_sqrt G *ᵥ g_aux G s =
      cut G s * (volume G univ)^2 := by
    rw [D_sqrt, dotProduct_mulVec_lapMatrix G hd, g_aux]
    set L := G.lapMatrix ℝ
    have h0 : L *ᵥ ↑(volume G s) = 0 := by
      rw [← mul_one ((volume G s) : V → ℝ), ← nsmul_eq_mul, mulVec_smul, G.lapMatrix_mulVec_const_eq_zero, smul_zero]
    have h0' : ↑(volume G s) ᵥ* L = 0 := by rw [← mulVec_transpose, G.isSymm_lapMatrix, h0]
    rw [mulVec_sub, h0, sub_zero, dotProduct_mulVec, sub_vecMul, h0', sub_zero, ← dotProduct_mulVec,
      ← nsmul_eq_mul, mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp_rw [cut_lapMatrix, nsmul_eq_mul]
    ring
  have h2 : ∑ i : V, (D_sqrt G *ᵥ g_aux G s) i ^ (2 : ℕ) =
      (volume G univ) * (volume G s) * (volume G sᶜ) := by
    simp [D_sqrt, mulVec_diagonal, mul_pow, g_aux, sub_sq]
    have hi : (v : V) → (Set.indicator s (1 : V → ℝ) v ^ 2 = Set.indicator s (1 : V → ℝ) v) := by
      simp [sq, Set.indicator_apply]
    simp_rw [hi, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
    conv_lhs => arg 1; arg 1; arg 2; intro v; rw [← mul_assoc, mul_comm, ← mul_assoc]
    conv_lhs => arg 1; arg 1; rw [← sum_mul]; tactic => simp [Set.indicator_apply]; rw [← Nat.cast_sum, ← volume]
    conv_lhs => arg 1; arg 2; arg 2; intro v; rw [← mul_assoc]
    conv_lhs => arg 1; arg 2; rw [← sum_mul];
    conv_lhs => arg 1; arg 2; arg 1; arg 2; intro v; rw [← mul_comm, ← mul_assoc, mul_assoc]
    conv_lhs => arg 1; arg 2; arg 1; rw [← mul_sum]; tactic => simp [Set.indicator_apply]; rw [← Nat.cast_sum, ← volume]
    conv_lhs => arg 2; rw [← sum_mul, ← Nat.cast_sum, ← volume]
    rw [volume_compl, Nat.cast_sub]
    ring
    apply volume_monotone; exact subset_univ s
  rw [h1, h2]
  calc
    _ = ↑(cut G s) * ↑(volume G univ) * (↑(volume G univ) / ↑(volume G univ)) / (↑(volume G s) * ↑(volume G sᶜ)) := by ring
    _ ≤ ↑(cut G s) * ↑(volume G univ) * (1 : ℝ) / (↑(volume G s) * ↑(volume G sᶜ)) := by rel [div_self_le_one ((volume G univ) : ℝ)]
    _ = ↑(cut G s) * ↑(volume G univ) / (↑(volume G s) * ↑(volume G sᶜ)) := by simp only [mul_one]
    _ = ↑(cut G s) * ↑(volume G univ) / ↑((volume G s) * (volume G sᶜ)) := by rw [Nat.cast_mul]
    _ ≤ ↑(cut G s) * ↑(volume G univ) / ↑(max (volume G s) (volume G sᶜ) * min (volume G s) (volume G sᶜ)) := by rw [max_mul_min]
    _ = ↑(cut G s) * ↑(volume G univ) / (↑(max (volume G s) (volume G sᶜ)) * ↑(min (volume G s) (volume G sᶜ))) := by rw [Nat.cast_mul]
    _ = ↑(cut G s) * (↑(volume G univ) / ↑(max (volume G s) (volume G sᶜ))) / ↑(min (volume G s) (volume G sᶜ)) := by ring;
    _ = ↑(cut G s) * ↑(volume G univ) * (1 / ↑(max (volume G s) (volume G sᶜ))) * (1 / ↑(min (volume G s) (volume G sᶜ))) := by ring
    _ ≤ ↑(cut G s) * ↑(2 * (max (volume G s) (volume G sᶜ))) * (1 / ↑(max (volume G s) (volume G sᶜ))) * (1 / ↑(min (volume G s) (volume G sᶜ))) := by gcongr; rel [volume_univ_le_max G s]
    _ = ↑(cut G s) * (2 * ↑(max (volume G s) (volume G sᶜ))) * (1 / ↑(max (volume G s) (volume G sᶜ))) * (1 / ↑(min (volume G s) (volume G sᶜ))) := by rw [Nat.cast_mul 2]; rfl
    _ = ↑(cut G s) * 2 * (↑(max (volume G s) (volume G sᶜ)) * (1 / ↑(max (volume G s) (volume G sᶜ)))) * (1 / ↑(min (volume G s) (volume G sᶜ))) := by simp_rw [one_div, mul_assoc]
    _ = ↑(cut G s) * 2 * (↑(max (volume G s) (volume G sᶜ)) / ↑(max (volume G s) (volume G sᶜ))) * (1 / ↑(min (volume G s) (volume G sᶜ))) := by rw [mul_div (↑(max (volume G s) (volume G sᶜ)) : ℝ), mul_one];
    _ ≤ ↑(cut G s) * 2 * 1 * (1 / ↑(min (volume G s) (volume G sᶜ))) := by rel [div_self_le_one ((↑(max (volume G s) (volume G sᶜ))) : ℝ)]
    _ = 2 * (↑(cut G s) / ↑(min (volume G s) (volume G sᶜ))) := by ring
    _ = 2 * (conductance G s) := by simp [conductance]
    _ ≤ 2 * (minConductance G) := by rw [hs];


theorem cheeger_ineq_easy : gap hV G ≤ 2 * (minConductance G : ℝ) := by
    obtain ⟨s, _, h⟩ := Finset.exists_mem_eq_inf' universe_powerSet_nonempty (conductance G)
    rw [← minConductance] at h
    apply LE.le.trans (gap_le_rayleigh hV G s) (rayleigh_le_minConductance G hd s (Eq.symm h))

end easy_inequality

----------------------------------------------------------------------------------------------------

section hard_inequality

variable [FinEnum V] [NeZero (FinEnum.card V)]

noncomputable abbrev R (f : V → ℝ) : ℝ := (∑ (u : V) (v : V) with G.Adj u v, (f u - f v) ^ 2) / (2 * ∑ v, f v^2 * G.degree v)

noncomputable def gap' : ℝ :=
  ⨅ f : {f : V → ℝ // ∑ v, f v = 0}, R G f

variable {g : V → ℝ}

-- def vertex_tuple : Fin (FinEnum.card V) → V := (@FinEnum.equiv V).invFun

/- maps i to the vertex that takes the i-th largest value when mapped by f -/
noncomputable def V_tuple (f : V → ℝ) : Fin (FinEnum.card V) → V :=
  (@FinEnum.equiv V).invFun ∘ Tuple.sort (f ∘ (@FinEnum.equiv V).invFun)

noncomputable def sweep (f : V → ℝ) (i : Fin (FinEnum.card V)) :=
  ((V_tuple f) '' {j : Fin (FinEnum.card V) | j < i}).toFinset

#check fun i : Finset.range (FinEnum.card V) => sweep g i

/- α_G = min_i h_(S_i) -/
noncomputable def minSweepConductance (f : V → ℝ) : NNReal :=
  {sweep f i | i : Fin (FinEnum.card V)}.toFinset.inf' (by rw [Set.toFinset_nonempty, ← Set.range, Set.range_nonempty_iff_nonempty, ← Fin.pos_iff_nonempty]; sorry) (conductance G)

/-
noncomputable def min_sweep_conductance (f : V → ℝ) : NNReal :=
  ⨅ i : Fin (FinEnum.card V), conductance G (sweep f i)
-/

/- h_G ≤ α_G -/
theorem minConductance_le_minSweepConductance (f : V → ℝ) :
    minConductance G ≤ (minSweepConductance G f) := by
  simp only [minConductance._eq_1, powerset_univ, minSweepConductance, Set.mem_setOf_eq,
    le_inf'_iff, inf'_le_iff, mem_univ, true_and]
  intro s _
  use s

#check {i : Fin (FinEnum.card V) | volume G (sweep _ i) ≤ (volume G univ) / 2}.toFinset.max

noncomputable def r (f : V → ℝ) : Fin (FinEnum.card V) := {i : Fin (FinEnum.card V) | volume G (sweep f i) ≤ (volume G univ) / 2}.toFinset.max' (sorry)

noncomputable def v_r (f : V → ℝ) : V := V_tuple f (r G f)

noncomputable def shift (f : V → ℝ) : V → ℝ := fun v => f v - f (v_r G f)

noncomputable def shift_pos_i (f : V → ℝ) : Fin (FinEnum.card V) → ℝ := ((shift G f)⁺ ∘ V_tuple f)

noncomputable def shift_neg_i (f : V → ℝ) : Fin (FinEnum.card V) → ℝ := ((shift G f)⁻ ∘ V_tuple f)

theorem posPart_sub_sq_add_negPart_sub_sq (u v : V) (f : V → ℝ) :
    (f⁺ u - f⁺ v) ^ 2 + (f⁻ u - f⁻ v) ^ 2 ≤ (f u - f v) ^ 2 := by
  simp_rw [Pi.oneLePart_apply, Pi.leOnePart_apply, posPart_eq_ite, negPart_eq_ite]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  · simp only [sub_neg_eq_add, add_le_iff_nonpos_right]
    have hu : f u = 0 := by rw [← LE.le.ge_iff_eq]; assumption; assumption
    have hv : f v = 0 := by rw [← LE.le.ge_iff_eq]; assumption; assumption
    simp only [hu, neg_zero, hv, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      le_refl]
  · simp only [sub_zero, even_two, Even.neg_pow, add_le_iff_nonpos_right]
    have hu : f u = 0 := by rw [← LE.le.ge_iff_eq]; assumption; assumption
    simp only [hu, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, le_refl]
  · simp only [sub_neg_eq_add, zero_add, add_le_iff_nonpos_right]
    have hv : f v = 0 := by rw [← LE.le.ge_iff_eq]; assumption; assumption
    simp only [hv, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, le_refl]
  · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    le_refl]
  · simp only [sub_zero, sub_neg_eq_add]
    have hu : f u = 0 := by rw [← LE.le.ge_iff_eq]; assumption; assumption
    simp only [hu, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_add,
      zero_sub, even_two, Even.neg_pow, le_refl]
  · push_neg at *
    apply lt_trans h7 at h2
    apply lt_irrefl at h2
    contradiction
  · simp only [sub_zero, sub_neg_eq_add, zero_add]
    push_neg at *
    rw [sub_sq', add_comm, le_sub_self_iff]
    apply mul_nonpos_of_nonneg_of_nonpos
    · apply mul_nonneg
      · apply Nat.ofNat_nonneg
      · assumption
    · assumption
  · simp only [sub_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero]
    push_neg at *
    apply lt_trans h8 at h2
    apply lt_irrefl at h2
    contradiction
  · simp only [zero_sub, even_two, Even.neg_pow, sub_neg_eq_add]
    push_neg at *
    have hv : f v = 0 := by rw [← LE.le.ge_iff_eq]; assumption; assumption
    simp only [hv, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, even_two,
      Even.neg_pow, zero_add, sub_zero, le_refl]
  · simp only [zero_sub, even_two, Even.neg_pow, sub_zero]
    push_neg at *
    rw [sub_sq', add_comm, le_sub_self_iff]
    apply mul_nonpos_of_nonpos_of_nonneg
    · apply mul_nonpos_of_nonneg_of_nonpos
      · apply Nat.ofNat_nonneg
      · assumption
    · assumption
  · simp only [zero_sub, even_two, Even.neg_pow, sub_neg_eq_add, zero_add]
    push_neg at *
    apply lt_trans h10 at h1
    apply lt_irrefl at h1
    contradiction
  · simp only [zero_sub, even_two, Even.neg_pow, sub_self, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero]
    push_neg at *
    apply lt_trans h10 at h1
    apply lt_irrefl at h1
    contradiction
  · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_neg_eq_add,
    zero_add]
    rw [← sub_eq_neg_add, sq_le_sq, abs_sub_comm]
  · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
    even_two, Even.neg_pow, zero_add]
    push_neg at *
    apply lt_trans h14 at h9
    apply lt_irrefl at h9
    contradiction
  · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_neg_eq_add,
    zero_add]
    push_neg at *
    apply lt_trans h13 at h1
    apply lt_irrefl at h1
    contradiction
  · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    push_neg at *
    apply lt_trans h15 at h9
    apply lt_irrefl at h9
    contradiction

theorem sum_sq_deg_le (hg : ∑ v, g v * G.degree v = 0) :
    ∑ v : V, g v ^ 2 * G.degree v ≤ ∑ v : V, (g v - g (v_r G g)) ^ 2 * G.degree v := by
  simp only [sub_sq', right_distrib, sub_mul, sum_add_distrib, sum_sub_distrib, add_sub_assoc]
  simp only [le_add_iff_nonneg_right, sub_nonneg]
  conv_lhs => arg 2; intro v; rw [mul_comm (2 * g v), mul_assoc, mul_assoc]
  rw [← mul_sum, ← mul_sum, hg, mul_zero, mul_zero]
  apply sum_nonneg
  intro v _
  apply mul_nonneg
  · apply sq_nonneg
  · apply Nat.cast_nonneg

#check ∑ (u : V) (v : V) with G.Adj u v, (g u - g v) ^ 2

theorem part1 (hg : R G g = gap' G) :
    R G ((shift G g)⁺) ≤ gap' G ∨ R G ((shift G g)⁻) ≤ gap' G := by
  rw [← min_le_iff, R, R]
  calc
    _ ≤ ((∑ (u : V) (v : V) with G.Adj u v, ((shift G g)⁺ u - (shift G g)⁺ v) ^ 2) + (∑ (u : V) (v : V) with G.Adj u v, ((shift G g)⁻ u - (shift G g)⁻ v) ^ 2)) / (2 * ∑ v : V, (shift G g)⁺ v ^ 2 * G.degree v + 2 * ∑ v : V, (shift G g)⁻ v ^ 2 * G.degree v) := by apply min_le_mediant; sorry; sorry
    _ = (∑ (u : V) (v : V) with G.Adj u v, (((shift G g)⁺ u - (shift G g)⁺ v) ^ 2 + ((shift G g)⁻ u - (shift G g)⁻ v) ^ 2)) / (2 * ∑ v : V, ((shift G g)⁺ v ^ 2 + (shift G g)⁻ v ^ 2) * G.degree v) := sorry
    _ ≤ (∑ (u : V) (v : V) with G.Adj u v, (shift G g u - shift G g v) ^ 2) / (2 * ∑ v : V, ((shift G g)⁺ v ^ 2 + (shift G g)⁻ v ^ 2) * G.degree v) := by apply div_le_div_of_nonneg_right (α := ℝ); gcongr; rw [← Pi.oneLePart_apply, ← Pi.leOnePart_apply]; apply posPart_sub_sq_add_negPart_sub_sq; apply mul_nonneg; apply Nat.ofNat_nonneg; apply sum_nonneg; intro v _; apply mul_nonneg; apply add_nonneg; apply sq_nonneg; apply sq_nonneg; apply Nat.cast_nonneg
    _ = (∑ (u : V) (v : V) with G.Adj u v, (g u - g v) ^ 2) / (2 * ∑ v : V, ((shift G g)⁺ v ^ 2 + (shift G g)⁻ v ^ 2) * G.degree v) := by congr; simp_rw [shift, sub_sub_sub_cancel_right]
    _ ≤ (∑ (u : V) (v : V) with G.Adj u v, (g u - g v) ^ 2) / (2 * ∑ v : V, ((shift G g)⁺ v - (shift G g)⁻ v) ^ 2 * G.degree v) := by gcongr; sorry; rw [sub_sq, add_le_add_iff_right, tsub_le_iff_right, le_add_iff_nonneg_right]; apply mul_nonneg; apply mul_nonneg; apply Nat.ofNat_nonneg; apply posPart_nonneg; apply negPart_nonneg
    _ ≤ (∑ (u : V) (v : V) with G.Adj u v, (g u - g v) ^ 2) / (2 * ∑ v : V, (shift G g v) ^ 2 * G.degree v) := by simp only [Pi.oneLePart_apply, Pi.leOnePart_apply, posPart_sub_negPart, le_refl]
    _ ≤ (∑ (u : V) (v : V) with G.Adj u v, (g u - g v) ^ 2) / (2 * ∑ v : V, g v ^ 2 * G.degree v) := by apply div_le_div_of_nonneg_left; sorry; sorry; rw [mul_le_mul_left]; unfold shift; apply sum_sq_deg_le; sorry; apply Nat.ofNat_pos
    _ = R G g := by rw [R]
    _ ≤ gap' G := by rw [hg]

lemma degree_eq (i : Fin (FinEnum.card V)) : (G.degree (V_tuple g i) : ℝ) = (volume G (sweep g i) : ℝ) - (volume G (sweep g (⟨i-1, sorry⟩)) : ℝ) := by
  unfold volume
  rw [Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sdiff_eq_sub (by unfold sweep; simp only [Set.mem_setOf_eq, Set.toFinset_image]; apply image_subset_image; sorry)]
  have hs : sweep g i \ sweep g ⟨i-1, sorry⟩ = {V_tuple g i} := by
    sorry
  rw [hs, Finset.sum_singleton]



lemma thm_one_dot_six (f : V → ℝ) : ∑ i, shift_pos_i G f i = ∑ (i : Finset.range (FinEnum.card V)), shift_pos_i G f i := by
  sorry

theorem part2_pos : (minSweepConductance G g : ℝ)^2 / 2 ≤ R G ((shift G g)⁺) := by
  set α := minSweepConductance G g
  calc
    _ = (α^2 / 2) * (∑ i, shift_pos_i G g i ^ 2 * G.degree (V_tuple g i)) ^ 2 / (∑ i, shift_pos_i G g i ^ 2 * G.degree (V_tuple g i)) ^ 2 := by sorry
    _ ≤ R G ((shift G g)⁺) := sorry

theorem part2_neg : (minSweepConductance G g : ℝ)^2 / 2 ≤ R G ((shift G g)⁻) := by
  sorry

/- α² / 2 ≤ λ, long chain of inequalities -/
theorem my_ineq2 {f : V → ℝ} (hf : R G f = gap' G) :
    (minSweepConductance G f : ℝ)^2 / 2 ≤ gap' G := by
  cases part1 G hf
  · calc
      _ ≤ R G (shift G f)⁺ := part2_pos G
      _ ≤ gap' G := by assumption
  · calc
      _ ≤ R G (shift G f)⁻ := part2_neg G
      _ ≤ gap' G := by assumption


/- h_G²/2 ≤ α²/2 ≤ λ -/
theorem cheeger_ineq_hard : (minConductance G : ℝ)^2 / 2 ≤ gap' G := by
  obtain ⟨f, hf⟩ := Module.End.HasEigenvalue.exists_hasEigenvector (gap_is_eig hV G) --(gap G hc).2

  have hf' : R G f = gap' G := sorry

  have h : minConductance G^2 / 2 ≤ (minSweepConductance G f)^2 / 2 := by
    simp [NNReal.le_div_iff_mul_le]
    rw [← NNReal.coe_le_coe]
    apply sq_le_sq' -- Theorem for NNReal?
    · apply sub_nonneg.1
      rw [sub_neg_eq_add]
      apply add_nonneg
      · simp only [NNReal.val_eq_coe, NNReal.zero_le_coe]
      · simp only [NNReal.val_eq_coe, NNReal.zero_le_coe]
    · exact minConductance_le_minSweepConductance G f
  calc
    (minConductance G)^2 / 2 ≤ (minSweepConductance G f : ℝ)^2 / 2 := h
    _ ≤ ↑(gap' G) := by exact my_ineq2 G hf'

end hard_inequality
