import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Spectrum

open BigOperators

section

open Matrix

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {A : Matrix E E ℝ} (hA : A.IsSymm) (hH : A.IsHermitian)

theorem IsSymm_toEuclidean_of_IsSymm (hA : A.IsSymm) : LinearMap.IsSymmetric (toEuclideanLin A) :=
  sorry

theorem hn : FiniteDimensional.finrank ℝ (E → ℝ) = Fintype.card E := by
  rw [FiniteDimensional.finrank_fintype_fun_eq_card]

/-
noncomputable def symm_matrix_eigenvalues_sorted (i : Fin (Fintype.card E)) : ℝ :=
  LinearMap.IsSymmetric.eigenvalues_sorted (IsSymm_toEuclidean_of_IsSymm A hA) hn i
-/

noncomputable def symm_matrix_eigenvalues_sorted (i : Fin (Fintype.card E)) : ℝ :=
  (Matrix.IsHermitian.eigenvalues₀ hH ∘ Tuple.sort (Matrix.IsHermitian.eigenvalues₀ hH)) i

theorem symm_matrix_eigenvalues_sorted_is_eig (i : Fin (Fintype.card E)) :
    Module.End.HasEigenvalue (Matrix.toLin' A) (symm_matrix_eigenvalues_sorted hA i) := by
  sorry

end

section

open LinearMap.IsSymmetric

variable {𝕜 : Type*} [RCLike 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

variable {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)

variable (hT : T.IsSymmetric) {n : ℕ} (hn : FiniteDimensional.finrank 𝕜 E = n)

noncomputable def eigenvalues' (i : Fin n) : ℝ :=
  (eigenvalues hT hn ∘ Tuple.sort (eigenvalues hT hn)) i

noncomputable def eigenvectorBasis' (i : Fin n) : E :=
  eigenvectorBasis hT hn (Tuple.sort (eigenvalues hT hn) i)

theorem my_thm (v : E) : ⟪T v, v⟫ =
    ∑ i : Fin n, (eigenvalues hT hn i) * ↑(‖(eigenvectorBasis hT hn).repr v i‖ ^ 2) := by
  rw [← OrthonormalBasis.sum_repr (eigenvectorBasis hT hn) (T v)]
  conv_lhs => arg 2; rw [← OrthonormalBasis.sum_repr (eigenvectorBasis hT hn) v]
  rw [Orthonormal.inner_sum]
  · simp only [eigenvectorBasis_apply_self_apply]
    simp only [map_mul, RCLike.conj_ofReal, RCLike.ofReal_sum, RCLike.ofReal_mul, RCLike.ofReal_pow]
    conv_lhs => arg 2; intro i; rw [mul_assoc, RCLike.conj_mul]
  · apply OrthonormalBasis.orthonormal

variable (h0 : 0 < n)

theorem name_later : (⨅ v : { v : E // v ≠ 0 }, RCLike.re ⟪T v, v⟫ / ‖(v : E)‖ ^ 2 : ℝ) =
  (⨅ x : { x : EuclideanSpace 𝕜 (Fin n) // x ≠ 0 },
    (∑ i : Fin n, (eigenvalues hT hn i) * ↑(‖x.1 i‖ ^ 2)) / ‖x.1‖ ^ 2) := by
  apply Equiv.iInf_congr (Equiv.subtypeEquiv ((eigenvectorBasis hT hn).repr).toEquiv (_))
  · intro v
    simp only [ne_eq, LinearEquiv.coe_toEquiv, LinearIsometryEquiv.coe_toLinearEquiv,
      AddEquivClass.map_eq_zero_iff, forall_const, Equiv.subtypeEquiv_apply]
    rw [_root_.my_thm hT hn v, RCLike.ofReal_re, LinearIsometryEquiv.norm_map]
  · intro v
    simp only [ne_eq, LinearEquiv.coe_toEquiv, LinearIsometryEquiv.coe_toLinearEquiv,
      AddEquivClass.map_eq_zero_iff]

theorem big_thm : _root_.eigenvalues' hT hn ⟨0, h0⟩ =
    (⨅ v : { v : E // v ≠ 0 }, RCLike.re ⟪T v, v⟫ / ‖(v : E)‖ ^ 2 : ℝ) := by
  rw [_root_.name_later hT hn]
  conv_rhs => arg 1; intro x; rw [← Equiv.sum_comp (Tuple.sort (eigenvalues hT hn)) _]
  apply le_antisymm
  · sorry -- apply le_ciInf
  · sorry -- apply ciInf_le

----------------------------------------------------------------------------------------------------

#check (𝕜 ∙ (_root_.eigenvectorBasis' hT hn ⟨0, h0⟩))ᗮ
#check (eigenvectorBasis hT hn).repr _
#check (eigenvectorBasis hT hn).repr.symm _

variable {m : ℕ} (hm : m ≤ n)
/-
noncomputable def my_equiv (i : Fin n) :
(𝕜 ∙ (eigenvectorBasis hT hn i))ᗮ ≃ EuclideanSpace 𝕜 (Fin (n-1)) :=
  { toFun := (eigenvectorBasis hT hn).repr, -- remove i-th component
    invFun := fun x => ⟨(eigenvectorBasis hT hn).repr.symm x, by sorry⟩, -- at x add 0 at i-th
    left_inv := sorry,
    right_inv := sorry }
-/

variable (i : Fin n)

#check hT.invariant_orthogonalComplement_eigenspace (hT.eigenvalues hn i)
#check T.restrict (hT.invariant_orthogonalComplement_eigenspace (hT.eigenvalues hn i))
#check Module.End.eigenspace_restrict_le_eigenspace T (hT.invariant_orthogonalComplement_eigenspace (hT.eigenvalues hn i)) (hT.eigenvalues hn i)

noncomputable def T_rest :=
  T.restrict (hT.invariant_orthogonalComplement_eigenspace (hT.eigenvalues hn i))

theorem rank_orth : FiniteDimensional.finrank 𝕜 (Module.End.eigenspace T (eigenvalues hT hn i))ᗮ = n - 1 := by
  sorry -- Submodule.finrank_add_finrank_orthogonal

#check ((hT.restrict_invariant (hT.invariant_orthogonalComplement_eigenspace (hT.eigenvalues hn i))).eigenvectorBasis (_root_.rank_orth hT hn i)).repr

noncomputable def the_equiv :=
  (((hT.restrict_invariant (hT.invariant_orthogonalComplement_eigenspace (hT.eigenvalues hn i))).eigenvectorBasis (_root_.rank_orth hT hn i)).repr).toEquiv

noncomputable def T_rest_eigenvalues :=
  (hT.restrict_invariant (hT.invariant_orthogonalComplement_eigenspace (hT.eigenvalues hn i))).eigenvalues (_root_.rank_orth hT hn i)

theorem name_later' :
  (⨅ v : { v : (Module.End.eigenspace T ↑(eigenvalues hT hn i))ᗮ // v ≠ 0 }, RCLike.re ⟪T v, v⟫ / ‖(v : E)‖ ^ 2 : ℝ) =
  (⨅ x : { x : EuclideanSpace 𝕜 (Fin (n-1)) // x ≠ 0 },
    (∑ j : Fin (n-1), (_root_.T_rest_eigenvalues hT hn i j) * ↑(‖x.1 j‖ ^ 2)) / ‖x.1‖ ^ 2) := by
  apply Equiv.iInf_congr (Equiv.subtypeEquiv (_root_.the_equiv hT hn i) (_))
  · intro v
    sorry
  · intro v
    simp only [ne_eq, _root_.the_equiv, LinearEquiv.coe_toEquiv, LinearIsometryEquiv.coe_toLinearEquiv,
      AddEquivClass.map_eq_zero_iff]

-- Could also directly use LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional

----------------------------------------------------------------------------------------------------
end
