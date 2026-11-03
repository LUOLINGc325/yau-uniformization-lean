import Yau.Proofs.P04CanonicalRegularity
import Yau.LeafProofs.L17RicciNaturality

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual canonical norm is smooth also at zeros of the section. -/
theorem canonicalNormSq_smooth (g : SmoothMetric M) (S : CanonicalSection M)
    (hS : IsHolomorphicCanonical S) : SmoothFn (canonicalNormSq g.form S) := by
  intro a
  have hc : ContDiffOn ℝ ∞ (canonicalCoeff S a) (chartTarget a) :=
    L17Holomorphic.real_contDiffOn_of_complexDiff (isOpen_extChartAt_target a) (hS a)
  have hd : ContDiffOn ℝ ∞ (fun z => (hMat g.form a z).det.re) (chartTarget a) :=
    Complex.reCLM.contDiff.comp_contDiffOn
      (L18Aux.contDiffOn_matrix_det (L18Aux.hMat_contDiffOn g a))
  have hnorm : ContDiffOn ℝ ∞ (fun z => ‖canonicalCoeff S a z‖^2) (chartTarget a) :=
    ContDiffOn.norm_sq (𝕜 := ℝ) hc
  apply (hnorm.div hd (fun z hz => (L18Aux.hMat_det_re_pos g.form a hz).ne')).congr
  intro z hz
  exact canonicalNormSq_inChart g.form S a hz

end Yau.Proofs.P04Aux
