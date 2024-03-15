import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.NormedSpace.Star.Matrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh


namespace Matrix

variable {𝕜 : Type*} [IsROrC 𝕜] {n : Type*} [Fintype n]

variable {A : Matrix n n 𝕜}

open scoped BigOperators

namespace IsHermitian

section DecidableEq

variable [DecidableEq n]

variable (hA : A.IsHermitian)

def Matrix.rayleighQuotient (A : Matrix n n 𝕜) (x : n → 𝕜) : 𝕜 := x ⬝ᵥ A *ᵥ x / x ⬝ᵥ x

theorem tofo (x : n → 𝕜) :  ContinuousLinearMap.rayleighQuotient (Matrix.toEuclideanCLM (𝕜 := 𝕜) A)
    ((WithLp.equiv 2 (n → 𝕜)).symm <| x) = Matrix.rayleighQuotient A x := sorry
