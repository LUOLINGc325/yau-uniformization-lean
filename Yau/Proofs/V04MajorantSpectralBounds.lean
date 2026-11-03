import Yau.Proofs.V04MajorantSeminorm

/-! Uniform spectral order bounds for the same smoothed symbol. The
upper constant depends only on the original symbol bound and fixed delta. -/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n : ℕ}

theorem matrix_real_algebraMap (c : ℝ) :
    algebraMap ℝ (CotangentMatrix n) c = (c : ℂ) • (1 : CotangentMatrix n) := by
  apply Matrix.ext
  intro i j
  simp [Algebra.algebraMap_eq_smul_one]

theorem smoothMajorant_upper_order {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (A : CotangentMatrix n) (hA : A.IsHermitian) (hbound : rectOpNorm A ≤ M) :
    ((((M + 2 * δ : ℝ) : ℂ) • (1 : CotangentMatrix n)) - smoothMajorant δ A).PosSemidef := by
  have hscalar : ∀ x ∈ spectrum ℝ A, scalarMajorant δ x ≤ M + 2 * δ := by
    intro x hx
    have hxnorm := IsometricContinuousFunctionalCalculus.norm_spectrum_le A hx
      (show IsSelfAdjoint A from hA)
    have hxabsA : |x| ≤ ‖A‖ := by simpa only [Real.norm_eq_abs] using hxnorm
    have hxabs : |x| ≤ M := hxabsA.trans hbound
    have hxmax : max x 0 ≤ M := max_le ((le_abs_self x).trans hxabs) hM
    have hh := (scalarMajorant_bounds hδ x).2.2.2
    linarith only [hh, hxmax, hδ]
  have hle := cfc_mono (a := A) (f := scalarMajorant δ) (g := fun _ : ℝ => M + 2 * δ)
    hscalar (scalarMajorant_contDiff hδ).continuous.continuousOn continuousOn_const
  rw [← smoothMajorant_eq_cfc δ A hA,
    cfc_const (M + 2 * δ) A (show IsSelfAdjoint A from hA)] at hle
  have hp := Matrix.le_iff.mp hle
  rw [matrix_real_algebraMap] at hp
  exact hp

end Yau.Blueprint.V04Proof
