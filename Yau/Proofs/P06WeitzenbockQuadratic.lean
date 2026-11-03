import Yau.Proofs.P06WeitzenbockGreen

noncomputable section
open MeasureTheory
open scoped Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G04Aux L03
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem gradientPair_nonneg (h : HermitianField M) (A : RealForm M 2) (x : M.Carrier) :
    0 ≤ gradientPair h A A x := by
  rw [gradientPair, chartGradientPair_eq_covTensorPair, L23Aux.covTensorPair_self]
  exact mul_nonneg (by norm_num) (L23Aux.covTensorNormSq_nonneg _
    (L12Aux.realMetricFn_posDef h x (chartPt x x) (mem_extChartAt_target x)) _)

theorem hodgePair_eq_global (h : HermitianField M) (hs : MetricSmooth h)
    (A B : RealForm M 2) (hA : SmoothRealForm A) (x : M.Carrier) :
    formInner h B (hodgeRealForm h 2 A) x = roughPair h A B x + curvaturePair h A B x := by
  have he := hodgePair_eq_rough_add_curvature h hs A B hA x (z := chartPt x x)
    (mem_extChartAt_target x)
  have hi : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  rw [hi] at he
  exact he

theorem curvaturePair_integrable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M 2)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    Integrable (curvaturePair g.form A B) μ := by
  have hs := L12Aux.metricSmooth_of_smoothMetric g
  have hh := smooth_compact_formInner_integrable g μ hμ B (hodgeRealForm g.form 2 A)
    hB (hodge_smooth g.form hs A hA) hcB
  have hr := roughPair_integrable g μ hμ A B hA hB hcB
  have he : curvaturePair g.form A B =
      fun x => formInner g.form B (hodgeRealForm g.form 2 A) x - roughPair g.form A B x := by
    funext x
    rw [hodgePair_eq_global g.form hs A B hA x]
    ring
  rw [he]
  exact hh.sub hr

/-- Global bilinear Weitzenböck Green formula in the original Riemannian
measure, proved from the density formula and a genuine finite partition. -/
theorem integral_hodgeTwo_weitzenbock (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M 2)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    (∫ x, formInner g.form (hodgeRealForm g.form 2 A) B x ∂μ) =
      (∫ x, gradientPair g.form A B x ∂μ) + ∫ x, curvaturePair g.form A B x ∂μ := by
  have hs := L12Aux.metricSmooth_of_smoothMetric g
  rw [formInner_symm g.form (hodgeRealForm g.form 2 A) B]
  calc
    _ = ∫ x, roughPair g.form A B x + curvaturePair g.form A B x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (hodgePair_eq_global g.form hs A B hA)
    _ = (∫ x, roughPair g.form A B x ∂μ) + ∫ x, curvaturePair g.form A B x ∂μ :=
      integral_add (roughPair_integrable g μ hμ A B hA hB hcB)
        (curvaturePair_integrable g μ hμ A B hA hB hcB)
    _ = _ := by rw [integral_rough_eq_gradient g μ hμ A B hA hB hcB]

theorem hodge_energy_bilinear (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M 2)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B)
    (hcA : CompactlySupportedRealForm A) (hcB : CompactlySupportedRealForm B) :
    (∫ x, formInner g.form (exteriorRealForm A) (exteriorRealForm B) x ∂μ) +
        (∫ x, formInner g.form (codifferentialRealForm g.form A) (codifferentialRealForm g.form B) x ∂μ) =
      (∫ x, gradientPair g.form A B x ∂μ) + ∫ x, curvaturePair g.form A B x ∂μ := by
  have he := integral_hodgeRealForm_succ_energy g μ hμ A B hA hB hcA hcB
  rw [integral_hodgeTwo_weitzenbock g μ hμ A B hA hB hcB] at he
  exact (add_comm _ _).trans he.symm

/-- The actual closed-form energy on its compact smooth core. In particular
this identity holds for every nonclosed signed real (1,1) input. -/
theorem hodge_energy_quadratic (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    (∫ x, formNormSq g.form (exteriorRealForm A) x ∂μ) +
        (∫ x, formNormSq g.form (codifferentialRealForm g.form A) x ∂μ) =
      (∫ x, gradientPair g.form A A x ∂μ) + ∫ x, curvaturePair g.form A A x ∂μ :=
  hodge_energy_bilinear g μ hμ A A hA hA hcA hcA

end Yau.NodeProofs.P06Weitzenbock
