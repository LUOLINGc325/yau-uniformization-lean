import Yau.Proofs.F04StaticLaplacian
import Yau.Proofs.F04CompactIntegral
import Yau.Proofs.F04ChartContinuity
import Yau.Proofs.F04DirichletCore

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem core_test_form_continuousOn (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ → HermitianField M)
    {I : Set ℝ} (hh : MetricFamilySmooth h I) {u v : M.Carrier → ℝ}
    (hu : SmoothFn u) (hv : SmoothFn v) (hcv : HasCompactSupport v) :
    ContinuousOn (fun t => -(∫ x, v x * laplacian (h t) u x ∂μ)) I := by
  let : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  have hL := metricFamily_static_laplacian_smooth h hh hu
  have hF : SmoothSpaceTime (fun x t => v x * laplacian (h t) u x) I := by
    intro c
    exact ((hv c).comp contDiffOn_fst (fun _ hp => hp.1)).mul (hL c)
  apply (compact_integral_continuousOn hcv (smoothSpaceTime_continuousOn hF) ?_).neg
  intro x t _ hx
  rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- Continuous time profiles of the actual nonsymmetric fixed-volume form.
Both arguments are the original supported smooth energy core. -/
def intrinsicCoreProfile (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ → HermitianField M) {T : ℝ}
    (hh : MetricFamilySmooth h (Icc 0 T)) (O : Set M.Carrier)
    (u v : dirichletCore g μ hμ O) : C(Icc (0 : ℝ) T, ℝ) where
  toFun := fun t => -(∫ x, v.val x * laplacian (h t) u.val x ∂μ)
  continuous_toFun := continuousOn_iff_continuous_domRestrict.mp
    (core_test_form_continuousOn g μ hμ h hh u.val.2.1 v.val.2.1 v.val.2.2)

end Yau.F04Proof
