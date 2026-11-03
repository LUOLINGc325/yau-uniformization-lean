import Yau.Proofs.F04ChartCoefficients

open Filter Set
open scoped Topology ContDiff Manifold Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L18Aux

/-- The actual Laplacian of a fixed smooth test function is jointly smooth
for the given Hermitian family, including the original closed time faces. -/
theorem metricFamily_static_laplacian_smooth {n : ℕ} {M : ComplexManifold n}
    (h : ℝ → HermitianField M) {I : Set ℝ} (hh : MetricFamilySmooth h I)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) :
    SmoothSpaceTime (fun x t => laplacian (h t) f x) I := by
  intro c
  have hO := isOpen_extChartAt_target (I := ComplexModel n) c
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (inChart c f)) (chartTarget c) :=
    (hf c).fderiv_of_isOpen hO (by simp)
  have hDD : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ (inChart c f))) (chartTarget c) :=
    hD.fderiv_of_isOpen hO (by simp)
  have hentry (i j : Yau.RIdx n) : ContDiffOn ℝ ∞
      (fun p : Point n => flowChartPrincipal h c p i j) (chartTarget c ×ˢ I) := by
    exact contDiffOn_const.mul (contDiffOn_matrix_inv (hh c)
      (fun p hp => (LeafProofs.L12Aux.realMetricFn_posDef (h p.2) c p.1 hp.1).det_pos.ne') i j)
  have hs : ContDiffOn ℝ ∞ (fun p : Point n => ∑ i, ∑ j,
      flowChartPrincipal h c p i j * fderiv ℝ (fderiv ℝ (inChart c f)) p.1
        (realVec i) (realVec j)) (chartTarget c ×ˢ I) := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact (hentry i j).mul (((hDD.clm_apply contDiffOn_const).clm_apply contDiffOn_const).comp
      contDiffOn_fst (fun _ hp => hp.1))
  apply hs.congr
  intro p hp
  exact flowChartPrincipal_operator h c hf p.1 hp.1 p.2

end Yau.F04Proof
