import Yau.Proofs.V03CompactIntegralOperator
import Yau.Proofs.V03CompactParamSmoothness

/-! The actual parameter mixed derivative commutes with circle averaging.
The compact trace is formed from the original jointly smooth density. -/

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V02CostMixedProof
open Yau Yau.Blueprint V03Proof

abbrev CircleAngleDomain := Set.Icc (0 : ℝ) (2 * Real.pi)

def circleAngleMeasure : Measure CircleAngleDomain :=
  (volume.restrict CircleAngleDomain).comap Subtype.val

instance : IsFiniteMeasure circleAngleMeasure := by
  letI : IsFiniteMeasure (volume.restrict CircleAngleDomain) :=
    isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  exact inferInstanceAs (IsFiniteMeasure ((volume.restrict CircleAngleDomain).comap
    (Subtype.val : CircleAngleDomain → ℝ)))

def circleAverageL : C(CircleAngleDomain, ℝ) →L[ℝ] ℝ :=
  (2 * Real.pi)⁻¹ • compactIntegralL circleAngleMeasure

theorem circleAverageL_eq (f : C(CircleAngleDomain, ℝ)) (g : ℝ → ℝ)
    (hfg : ∀ θ : CircleAngleDomain, f θ = g θ) :
    circleAverageL f = circleAverage g := by
  change (2 * Real.pi)⁻¹ * (∫ θ : CircleAngleDomain, f θ ∂circleAngleMeasure) = _
  rw [circleAverage, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  congr 1
  calc
    _ = ∫ θ : CircleAngleDomain, g θ ∂circleAngleMeasure :=
      integral_congr_ae (Eventually.of_forall hfg)
    _ = ∫ θ in CircleAngleDomain, g θ := by
      rw [circleAngleMeasure, integral_subtype_comap measurableSet_Icc,
        Measure.restrict_restrict measurableSet_Icc, Set.inter_self]
    _ = ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), g θ := integral_Icc_eq_integral_Ioc

theorem circleAverage_compactParamTrace {U : Set ℂ} {f : ℂ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ CircleAngleDomain)) {z : ℂ} (hz : z ∈ U) :
    circleAverageL (compactParamTrace hf.continuousOn z) =
      circleAverage (fun θ => f (z, θ)) :=
  circleAverageL_eq _ _ (compactParamTrace_apply hf.continuousOn hz)

theorem circleAverage_contDiffOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ CircleAngleDomain)) :
    ContDiffOn ℝ ∞ (fun z => circleAverage (fun θ => f (z, θ))) U := by
  have hT := compactParamTrace_contDiffOn hU (uniqueDiffOn_Icc Real.two_pi_pos) hf
  exact (circleAverageL.contDiff.comp_contDiffOn hT).congr
    (fun z hz => (circleAverage_compactParamTrace hf hz).symm)

theorem mixedReal_circleAverage {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ CircleAngleDomain)) (h0 : (0 : ℂ) ∈ U) :
    mixedReal (fun z => circleAverage (fun θ => f (z, θ))) =
      circleAverage (fun θ => mixedReal (fun z => f (z, θ))) := by
  let T := compactParamTrace hf.continuousOn
  have hT : ContDiffAt ℝ 2 T 0 :=
    ((compactParamTrace_contDiffOn hU (uniqueDiffOn_Icc Real.two_pi_pos) hf).contDiffAt
      (hU.mem_nhds h0)).of_le (by simp)
  have heq : (fun z => circleAverage (fun θ => f (z, θ))) =ᶠ[𝓝 0]
      (fun z => circleAverageL (T z)) := by
    filter_upwards [hU.mem_nhds h0] with z hz
    exact (circleAverage_compactParamTrace hf hz).symm
  rw [mixedReal_congr heq, mixedReal_comp_realCLM circleAverageL hT]
  change (1 / 4 : ℝ) • circleAverageL
    (fderiv ℝ (fderiv ℝ T) 0 1 1 + fderiv ℝ (fderiv ℝ T) 0 Complex.I Complex.I) = _
  rw [← map_smul]
  apply circleAverageL_eq
  intro θ
  have hpoint : (fun z => T z θ) =ᶠ[𝓝 0] (fun z => f (z, θ)) := by
    filter_upwards [hU.mem_nhds h0] with z hz
    exact compactParamTrace_apply hf.continuousOn hz θ
  have hEval := mixedReal_comp_realCLM (ContinuousMap.evalCLM ℝ θ) hT
  simp only [ContinuousMap.evalCLM_apply] at hEval
  have hmix := mixedReal_congr hpoint
  rw [hEval] at hmix
  simpa only [ContinuousMap.add_apply, ContinuousMap.smul_apply,
    smul_eq_mul, ContinuousMap.evalCLM_apply] using hmix

end Yau.Blueprint.V02CostMixedProof
