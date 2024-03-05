import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Matrix.Symmetric

open Matrix

variable {E : Type*} [Fintype E] [DecidableEq E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E]

variable {n : ℕ} (hn : FiniteDimensional.finrank ℝ (E → ℝ) = n)

variable (A : Matrix E E ℝ) (hA : A.IsSymm)

theorem IsSymm_toEuclidean_of_IsSymm (hA : A.IsSymm) : LinearMap.IsSymmetric (toEuclideanLin A) :=
  sorry

noncomputable def symm_matrix_eigenvalues_sorted (i : Fin n) : ℝ :=
  LinearMap.IsSymmetric.eigenvalues_sorted (IsSymm_toEuclidean_of_IsSymm A hA) hn i


#check (ℝ ∙ ((WithLp.equiv 2 _).symm <| fun _ ↦ 1 : E → ℝ))ᗮ

#check ((WithLp.equiv 2 _).symm <| fun _ ↦ 1 : E → ℝ)
