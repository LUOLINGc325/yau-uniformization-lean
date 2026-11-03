import Yau.Proofs.C05IntrinsicTensorNorm
import Yau.Proofs.C05RicciPropagationDefinitions
import Yau.Proofs.C05RicciSquareRealNorm
import Yau.LeafProofs.L23JetNaturality

/-! Actual scalar and Ricci jet norms agree with their fixed-chart expressions.
Thus intrinsic tube bounds can be used without differentiating chosen charts. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
open Yau.Proofs.C05HessianPropagationAux Yau.Proofs.C05RicciPropagationAux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem scalarJet_chart_change (k : HermitianField M) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (m : ℕ) (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    scalarJet k f c m z = tensorFrameTransform (realChartJacobian c d z)
      (scalarJet k f d m (realChartChange c d z)) := by
  apply tensorEvalCLM_injective
  rw [scalarJet_eval_chart_change k hk f hf m c d hz hy]
  exact (tensorEvalCLM_frameTransform _ _).symm

theorem scalarJet_norm_inChart (k : HermitianField M) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (m : ℕ) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    metricTensorNorm (realMetricFn k c z) (scalarJet k f c m z) =
      scalarJetNorm k f m (chartInv c z) := by
  let d := chartInv c z
  have hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source := mem_extChartAt_source d
  rw [scalarJet_chart_change k hk f hf m c d hz hy]
  unfold metricTensorNorm scalarJetNorm
  rw [covTensorNormSq_frameTransform _ _ _ (inverseMetric_chart_change k c d hz hy)]
  rfl

theorem realRicciJet_contDiffOn (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (m : ℕ) (v : Fin (2+m) → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => realRicciJet k c m z v) (chartTarget c) := by
  induction m with
  | zero => exact ricciTensor_contDiffOn k hk c v
  | succ m ih => exact covariantD_contDiffOn k hk c (realRicciJet k c m) ih v

theorem realRicciJet_eval_chart_change (k : HermitianField M) (hk : MetricSmooth k)
    (m : ℕ) (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    tensorEvalCLM (realRicciJet k c m z) =
      (tensorEvalCLM (realRicciJet k d m (realChartChange c d z))).compContinuousLinearMap
        (fun _ : Fin (2+m) => fderiv ℝ (realChartChange c d) z) := by
  induction m generalizing z with
  | zero => exact ricciTensor_eval_chart_change k hk c d hz hy
  | succ m ih =>
      apply covariantD_chart_change k hk c d (realRicciJet k c m) (realRicciJet k d m) hz hy
      · intro v
        exact ((realRicciJet_contDiffOn k hk c m v).contDiffAt
          ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      · intro v
        have hd : realChartChange c d z ∈ chartTarget d :=
          (extChartAt (ComplexModel n) d).map_source hy
        exact ((realRicciJet_contDiffOn k hk d m v).contDiffAt
          ((isOpen_extChartAt_target (I := ComplexModel n) d).mem_nhds hd)).differentiableAt (by simp)
      · intro w hw
        exact ih hw.1 hw.2

theorem realRicciJet_chart_change (k : HermitianField M) (hk : MetricSmooth k)
    (m : ℕ) (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    realRicciJet k c m z = tensorFrameTransform (realChartJacobian c d z)
      (realRicciJet k d m (realChartChange c d z)) := by
  apply tensorEvalCLM_injective
  rw [realRicciJet_eval_chart_change k hk m c d hz hy]
  exact (tensorEvalCLM_frameTransform _ _).symm

theorem realRicciJet_norm_inChart (k : HermitianField M) (hk : MetricSmooth k)
    (m : ℕ) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    metricTensorNorm (realMetricFn k c z) (realRicciJet k c m z) =
      realRicciJetNorm k m (chartInv c z) := by
  let d := chartInv c z
  have hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source := mem_extChartAt_source d
  rw [realRicciJet_chart_change k hk m c d hz hy]
  unfold metricTensorNorm realRicciJetNorm
  rw [covTensorNormSq_frameTransform _ _ _ (inverseMetric_chart_change k c d hz hy)]
  rfl

theorem ricciNormSq_inChart (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    inChart c (ricciNormSq k) z = (1/2:ℝ) *
      covTensorNormSq (realMetricFn k c z) (realRicciJet k c 0 z) := by
  let d := chartInv c z
  have hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source := mem_extChartAt_source d
  change ricciNormSq k d = _
  rw [ricciNormSq_eq_half_realRicciNormSq k hk hK d,
    realRicciJet_chart_change k hk 0 c d hz hy,
    covTensorNormSq_frameTransform _ _ _ (inverseMetric_chart_change k c d hz hy)]
  rfl

end Yau.Proofs.C05Aux
