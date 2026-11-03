import Yau.LeafProofs.L23RmNaturality
import Yau.LeafProofs.L23TensorFrameContraction

/-! The original iterated curvature derivatives have coordinate-independent
metric contraction, under MetricSmooth alone. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {M : ComplexManifold n}

theorem tensorEvalCLM_frameTransform (J : ComplexVector n →L[ℝ] ComplexVector n)
    (A : CovTensor n r) :
    tensorEvalCLM (tensorFrameTransform (realLinearMatrix J) A)=
      (tensorEvalCLM A).compContinuousLinearMap (fun _ : Fin r => J) := by
  have hc : tensorFrameTransform (realLinearMatrix J) A=
      (fun v : Fin r → RIdx n =>
        ((tensorEvalCLM A).compContinuousLinearMap (fun _ : Fin r => J))
          (fun j => realVec (v j))) := by
    funext v
    simp only [tensorFrameTransform,realLinearMatrix,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,tensorEvalCLM_apply]
  rw [hc,tensorEvalCLM_coefficients]

theorem rmJet_eval_chart_change (h : HermitianField M) (hh : MetricSmooth h)
    (k : ℕ) (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    tensorEvalCLM (rmJet h c k z)=
      (tensorEvalCLM (rmJet h d k (L12Aux.realChartChange c d z))).compContinuousLinearMap
        (fun _ : Fin (4+k) => fderiv ℝ (L12Aux.realChartChange c d) z) := by
  induction k generalizing z with
  | zero =>
      change tensorEvalCLM (rmTensor h c z)=_
      rw [rmTensor_chart_change h hh c d hz hy]
      exact tensorEvalCLM_frameTransform _ _
  | succ k ih =>
      change tensorEvalCLM (covariantD h c (rmJet h c k) z)=_
      apply covariantD_chart_change h hh c d (rmJet h c k) (rmJet h d k) hz hy
      · intro v
        exact ((rmJet_contDiffOn h hh c k v).contDiffAt
          ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      · intro v
        have hzD : L12Aux.realChartChange c d z ∈ chartTarget d :=
          (extChartAt (ComplexModel n) d).map_source hy
        exact ((rmJet_contDiffOn h hh d k v).contDiffAt
          ((isOpen_extChartAt_target (I := ComplexModel n) d).mem_nhds hzD)).differentiableAt (by simp)
      · intro w hw
        exact ih hw.1 hw.2

theorem rmJet_chart_change (h : HermitianField M) (hh : MetricSmooth h)
    (k : ℕ) (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    rmJet h c k z=tensorFrameTransform (realChartJacobian c d z)
      (rmJet h d k (L12Aux.realChartChange c d z)) := by
  apply tensorEvalCLM_injective
  rw [rmJet_eval_chart_change h hh k c d hz hy]
  exact (tensorEvalCLM_frameTransform _ _).symm

theorem chartJetSq_chart_change (h : HermitianField M) (hh : MetricSmooth h)
    (k : ℕ) (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    covTensorNormSq (realMetricFn h c z) (rmJet h c k z)=
      covTensorNormSq (realMetricFn h d (L12Aux.realChartChange c d z))
        (rmJet h d k (L12Aux.realChartChange c d z)) := by
  rw [rmJet_chart_change h hh k c d hz hy]
  exact covTensorNormSq_frameTransform _ _ _ (inverseMetric_chart_change h c d hz hy) _

theorem jetSq_inChart (h : HermitianField M) (hh : MetricSmooth h)
    (k : ℕ) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    inChart c (jetSq h k) z=
      covTensorNormSq (realMetricFn h c z) (rmJet h c k z) := by
  let d := chartInv c z
  have hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source := mem_extChartAt_source d
  have hch := chartJetSq_chart_change h hh k c d hz hy
  exact hch.symm

end Yau.LeafProofs.L23Aux
