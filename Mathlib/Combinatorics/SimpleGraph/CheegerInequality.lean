import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Function.Indicator
import Mathlib.Analysis.NormedSpace.Star.Matrix
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.InnerProductSpace.CourantFischer


open BigOperators Finset Matrix

variable {V : Type*} (α : Type*)
variable [Fintype V] [Nonempty V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable [Field α] [AddGroupWithOne α] -- Field makes spectrum_finset work

def volume (s : Finset V) : ℕ := ∑ v in s, G.degree v

/-
def edge_boundary (s : Set V) : Set (V × V) := {(u, v) | (u ∈ s) ∧ v ∉ s ∧ G.Adj u v}

-- Where to provide the proof that this is a set of edges?
def edge_boundary_v2 (s : Set V) : Set (SimpleGraph.edgeSet G) := Sym2.mk '' (edge_boundary G s)
-/

def cut (s : Finset V) : ℕ := ∑ u in s, ∑ v in sᶜ, (if G.Adj u v then 1 else 0)

noncomputable def conductance (s : Finset V) : α := cut G s / min (volume G s) (volume G sᶜ)

lemma universe_powerSet_nonempty : (Finset.powerset (Finset.univ : Finset V)).Nonempty := by
  apply Finset.powerset_nonempty

-- Will need the set which attains the minimum
noncomputable def min_conductance : ℝ := (Finset.powerset (Finset.univ : Finset V)).inf'
  (universe_powerSet_nonempty) (conductance ℝ G)

noncomputable def eigenvalues_finset : Finset (Module.End.Eigenvalues (Matrix.toLin' (G.lapMatrix α)))
  := Finset.univ

-- how to make this work for α?
noncomputable def pos_eigenvalues :=
  Set.toFinset {x : Module.End.Eigenvalues (Matrix.toLin' (G.lapMatrix ℝ)) | x > (0 : ℝ)}

-- how to get rid of this?
variable [LinearOrder (Module.End.Eigenvalues (toLin' (SimpleGraph.lapMatrix ℝ G)))]

noncomputable def spectral_gap := (pos_eigenvalues G).min' sorry

noncomputable def my_vector (s : Finset V): V → ℝ := (Set.indicator s 1) - (fun _ => (volume G s : ℝ)/(volume G univ))

noncomputable def LapMatrixCLM := (Matrix.toEuclideanCLM (𝕜 := ℝ) (G.lapMatrix ℝ))

-- Orthogonal complement of D^(1/2) 1
noncomputable def my_submodule := (ℝ ∙ ((WithLp.equiv 2 _).symm <| ((Real.sqrt ∘ (G.degree ·)) * (fun _ ↦ 1 : V → ℝ))))ᗮ

-- λ = inf R(g) over g ⟂ D^(1/2) 1
theorem qwertz : spectral_gap G = sInf (ContinuousLinearMap.rayleighQuotient (LapMatrixCLM G) '' (my_submodule G)) := sorry

-- λ ≤ R(g)
theorem gap_leq_rayleigh (s : Finset V) (hs : conductance ℝ G s = min_conductance G) :
  spectral_gap G ≤ ContinuousLinearMap.rayleighQuotient (LapMatrixCLM G) (my_vector G s) := by
  rw [qwertz]
  sorry

-- R(g) ≤ 2 * h
theorem rayleigh_leq_my_vec (s : Finset V) (hs : conductance ℝ G s = min_conductance G) :
  ContinuousLinearMap.rayleighQuotient (LapMatrixCLM G) (my_vector G s) ≤ 2 * (min_conductance G) := sorry

theorem cheeger_ineq_easy : spectral_gap G ≤ 2 * (min_conductance G) := by
  obtain ⟨s, _, h⟩ := Finset.exists_mem_eq_inf' universe_powerSet_nonempty (conductance ℝ G)
  rw [← min_conductance] at h
  apply LE.le.trans (gap_leq_rayleigh G s (Eq.symm h)) (rayleigh_leq_my_vec G s (Eq.symm h))

theorem cheeger_ineq_hard : min_conductance G^2 / 2 ≤ spectral_gap G := sorry




variable {n : ℕ} (hn : FiniteDimensional.finrank ℝ (V → ℝ) = n)

#check symm_matrix_eigenvalues_sorted hn (G.lapMatrix ℝ) (G.isSymm_lapMatrix)


#check (ℝ ∙ ((WithLp.equiv 2 _).symm <| ((Real.sqrt ∘ (G.degree ·)) * (fun _ ↦ 1 : V → ℝ))))ᗮ

#check ((WithLp.equiv 2 _).symm <| ((Real.sqrt ∘ (G.degree ·)) * (fun _ ↦ 1 : V → ℝ)))

#check {x : (my_submodule G) | x ≠ 0}
