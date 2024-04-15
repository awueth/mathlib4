import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Spectrum

open Matrix BigOperators


section

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
