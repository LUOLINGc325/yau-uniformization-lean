import Yau.Proofs.P03PoleSequence

/-! Fatou applies to the same scalar function and the actual regularized coordinate poles. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace Yau.Proofs.C03Aux.PoleLimit
open Yau Yau.NodeProofs.P03Aux
variable {n : ℕ}

theorem coordinate_pole_fatou (f : ComplexVector n → ℂ)
    (θ : ComplexVector n → ComplexVector n) (φ : ComplexVector n → ℝ) (R B : ℝ)
    (hθ : ContinuousOn θ (Metric.ball 0 R)) (hφ : ContinuousOn φ (Metric.ball 0 R))
    (hf : AEStronglyMeasurable f ((volume : Measure (ComplexVector n)).restrict (Metric.ball 0 R)))
    (hb : ∀ j : ℕ, (∫⁻ z in Metric.ball (0 : ComplexVector n) R,
      ENNReal.ofReal (‖f z‖ ^ 2 * Real.exp (-φ z) *
        Real.exp (-((n + 1 : ℕ) : ℝ) * Real.log (‖θ z‖ ^ 2 + poleEpsilon j)))) ≤
          ENNReal.ofReal B) :
    (∫⁻ z in Metric.ball (0 : ComplexVector n) R,
      ENNReal.ofReal (‖f z‖ ^ 2 * Real.exp (-φ z) *
        (‖θ z‖ ^ (2 * (n + 1)))⁻¹)) ≤ ENNReal.ofReal B := by
  let μ := (volume : Measure (ComplexVector n)).restrict (Metric.ball 0 R)
  let m := n + 1
  let g := fun (j : ℕ) (z : ComplexVector n) =>
    ENNReal.ofReal (‖f z‖ ^ 2 * Real.exp (-φ z) *
      Real.exp (-((m : ℝ) * Real.log (‖θ z‖ ^ 2 + poleEpsilon j))))
  have hθm : AEMeasurable θ μ := hθ.aemeasurable measurableSet_ball
  have hφm : AEMeasurable φ μ := hφ.aemeasurable measurableSet_ball
  have hg (j : ℕ) : AEMeasurable (g j) μ := by
    have hq := (hθm.norm.pow_const 2).add_const (poleEpsilon j)
    have hl := Real.measurable_log.comp_aemeasurable hq
    have he := Real.measurable_exp.comp_aemeasurable ((hl.const_mul (m : ℝ)).neg)
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (((hf.norm.aemeasurable.pow_const 2).mul
        (Real.measurable_exp.comp_aemeasurable hφm.neg)).mul he)
  have hp (z : ComplexVector n) :
      ENNReal.ofReal (‖f z‖ ^ 2 * Real.exp (-φ z) * (‖θ z‖ ^ (2 * m))⁻¹) ≤
        liminf (fun j => g j z) atTop := by
    by_cases hz : θ z = 0
    · simp only [hz, norm_zero, zero_pow (by dsimp [m]; omega : 2 * m ≠ 0),
        inv_zero, mul_zero, ENNReal.ofReal_zero]
      exact bot_le
    · have hn : ‖θ z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      have hq : Tendsto (fun j => ‖θ z‖ ^ 2 + poleEpsilon j) atTop (𝓝 (‖θ z‖ ^ 2)) := by
        simpa only [add_zero] using tendsto_const_nhds.add poleEpsilon_tendsto_zero
      have ht := Real.continuous_exp.continuousAt.tendsto.comp
        (((hq.log (pow_ne_zero 2 hn)).const_mul (m : ℝ)).neg)
      have he : Real.exp (-((m : ℝ) * Real.log (‖θ z‖ ^ 2))) =
          (‖θ z‖ ^ (2 * m))⁻¹ := by
        rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (sq_pos_of_ne_zero hn), ← pow_mul]
      have hlim : Tendsto (fun j => g j z) atTop
          (𝓝 (ENNReal.ofReal (‖f z‖ ^ 2 * Real.exp (-φ z) *
            (‖θ z‖ ^ (2 * m))⁻¹))) := by
        simpa only [g, he, Function.comp_def] using
          ENNReal.continuous_ofReal.continuousAt.tendsto.comp
            (ht.const_mul (‖f z‖ ^ 2 * Real.exp (-φ z)))
      exact hlim.liminf_eq.ge
  calc
    _ ≤ ∫⁻ z, liminf (fun j => g j z) atTop ∂μ := lintegral_mono hp
    _ ≤ liminf (fun j => ∫⁻ z, g j z ∂μ) atTop := lintegral_liminf_le' hg
    _ ≤ limsup (fun j => ∫⁻ z, g j z ∂μ) atTop := liminf_le_limsup
    _ ≤ ENNReal.ofReal B := limsup_le_of_le (h := Eventually.of_forall (by
      intro j
      simpa only [g, μ, m, neg_mul] using hb j))

end Yau.Proofs.C03Aux.PoleLimit
