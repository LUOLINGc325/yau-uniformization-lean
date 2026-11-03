import Yau.Proofs.P06FiberApproximationForms

noncomputable section
open Set
open scoped Topology InnerProductSpace
namespace Yau.NodeProofs.P06Aux.FiberApprox
open Yau Yau.LeafProofs Clip
variable {n : ℕ} {M : ComplexManifold n}

/-- A global intrinsic Hilbert--Schmidt bound, independent of every eigenframe choice. -/
theorem exists_global_pointNorm_bound (g : SmoothMetric M) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (h11 : RealOneOne A) :
    ∃ R : ℝ, 0 < R ∧ ∀ x, ‖pointFormHS g.form A x‖ ≤ R := by
  obtain ⟨B, hB⟩ := (L03.formNormSq_continuous g A hA).bddAbove_range_of_hasCompactSupport
    (L03.formNormSq_hasCompactSupport g.form A hcA)
  refine ⟨max B 0 + 1, by positivity, ?_⟩
  intro x
  have hb : formNormSq g.form A x ≤ B := hB (mem_range_self x)
  rw [formNormSq_eq_pointFormHS g.form A h11 x] at hb
  have hm : B ≤ max B 0 := le_max_left _ _
  have hp : 0 ≤ max B 0 := le_max_right _ _
  nlinarith [norm_nonneg (pointFormHS g.form A x)]

/-- One bound simultaneously controls the actual entry norm and all canonical eigenvalues. -/
theorem exists_global_spectral_and_pointNorm_bound (g : SmoothMetric M) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (h11 : RealOneOne A) :
    ∃ R : ℝ, 0 < R ∧ (∀ x, ‖pointFormHS g.form A x‖ ≤ R) ∧
      ∀ x i, (whiteHermitian g.form A h11 x).eigenvalues i ∈ Icc (-R) R := by
  obtain ⟨R, hR, hnorm⟩ := exists_global_pointNorm_bound g A hA hcA h11
  refine ⟨R, hR, hnorm, ?_⟩
  intro x i
  exact abs_le.mp ((abs_eigenvalues_le_matrixToHS _ (whiteHermitian g.form A h11 x) i).trans (hnorm x))

end Yau.NodeProofs.P06Aux.FiberApprox
