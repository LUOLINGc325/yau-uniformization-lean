import Yau.Proofs.F04CoreFormContinuity
import Yau.Proofs.F04LaplacianLinear
import Yau.Proofs.F04AdjointGlobal

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem compact_test_laplacian_integrable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (H : HermitianField M) (hH : MetricSmooth H)
    {u v : M.Carrier → ℝ} (hu : SmoothFn u) (hv : SmoothFn v) (hcv : HasCompactSupport v) :
    Integrable (fun x => v x * laplacian H u x) μ := by
  let := riemannianVolume_locallyFinite g μ hμ
  exact (continuous_of_smoothFn (smoothFn_mul hv (Adjoint.smoothFn_laplacian H hH hu))).integrable_of_hasCompactSupport hcv.mul_right

/-- The original core test form is genuinely bilinear with values in the
 space of continuous physical time profiles. -/
def intrinsicCoreBilinearProfile (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ → HermitianField M) {T : ℝ}
    (hh : MetricFamilySmooth h (Icc 0 T)) (O : Set M.Carrier) :
    dirichletCore g μ hμ O →ₗ[ℝ] dirichletCore g μ hμ O →ₗ[ℝ] C(Icc (0 : ℝ) T, ℝ) where
  toFun u :=
    { toFun := intrinsicCoreProfile g μ hμ h hh O u
      map_add' := by
        intro v w
        ext t
        have hi (k : dirichletCore g μ hμ O) := compact_test_laplacian_integrable g μ hμ (h t)
          (metricFamilySmooth_slice h _ hh t t.property) u.val.2.1 k.val.2.1 k.val.2.2
        change -(∫ x, (v.val x + w.val x) * laplacian (h t) u.val x ∂μ) =
          -(∫ x, v.val x * laplacian (h t) u.val x ∂μ) + -(∫ x, w.val x * laplacian (h t) u.val x ∂μ)
        simp_rw [add_mul]
        rw [integral_add (hi v) (hi w)]
        ring
      map_smul' := by
        intro c v
        ext t
        change -(∫ x, (c * v.val x) * laplacian (h t) u.val x ∂μ) =
          c * -(∫ x, v.val x * laplacian (h t) u.val x ∂μ)
        simp_rw [mul_assoc]
        rw [integral_const_mul]
        ring }
  map_add' := by
    intro u w
    ext v t
    have hi (k : dirichletCore g μ hμ O) := compact_test_laplacian_integrable g μ hμ (h t)
      (metricFamilySmooth_slice h _ hh t t.property) k.val.2.1 v.val.2.1 v.val.2.2
    change -(∫ x, v.val x * laplacian (h t) (fun y => u.val y + w.val y) x ∂μ) =
      -(∫ x, v.val x * laplacian (h t) u.val x ∂μ) + -(∫ x, v.val x * laplacian (h t) w.val x ∂μ)
    simp_rw [laplacian_add_smooth (h t) u.val.2.1 w.val.2.1, mul_add]
    rw [integral_add (hi u) (hi w)]
    ring
  map_smul' := by
    intro c u
    ext v t
    change -(∫ x, v.val x * laplacian (h t) (fun y => c * u.val y) x ∂μ) =
      c * -(∫ x, v.val x * laplacian (h t) u.val x ∂μ)
    simp_rw [laplacian_smul_smooth (h t) u.val.2.1, mul_left_comm (v.val _) c]
    rw [integral_const_mul]
    ring

end Yau.F04Proof
