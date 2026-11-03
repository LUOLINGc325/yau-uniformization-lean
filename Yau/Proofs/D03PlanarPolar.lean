import Yau.Proofs.D03PlanarMean

open scoped Topology RealInnerProductSpace ENNReal
open MeasureTheory Set Filter Metric

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau

theorem holomorphic_circle_lintegral_lower {q : ℕ}
    (F : ℂ → ComplexVector q) {U : Set ℂ} (hF : DifferentiableOn ℂ F U)
    (z : ℂ) (a : ℝ) (ha : 0 < a) (hball : closedBall z a ⊆ U) :
    ENNReal.ofReal (2 * Real.pi * ‖F z‖ ^ 2) ≤
      ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (‖F (circleMap z a θ)‖ ^ 2) ∂volume := by
  have hc : ContinuousOn F (sphere z a) :=
    hF.continuousOn.mono (sphere_subset_closedBall.trans hball)
  have hcont : Continuous (fun θ : ℝ => ‖F (circleMap z a θ)‖ ^ 2) := by
    apply Continuous.pow
    apply Continuous.norm
    apply hc.comp_continuous (continuous_circleMap z a)
    intro θ
    simpa only [abs_of_pos ha] using circleMap_mem_sphere' z a θ
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hint : IntegrableOn (fun θ : ℝ => ‖F (circleMap z a θ)‖ ^ 2)
      (Ioo (-Real.pi) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hpi).1 (hcont.intervalIntegrable _ _)
  have havg := Real.circleAverage_eq_integral_add (f := fun w => ‖F w‖ ^ 2)
    (c := z) (R := a) (-Real.pi)
  rw [intervalIntegral.integral_comp_add_right (f := fun θ : ℝ => ‖F (circleMap z a θ)‖ ^ 2), zero_add,
    show 2 * Real.pi + -Real.pi = Real.pi by ring,
    intervalIntegral.integral_of_le hpi, integral_Ioc_eq_integral_Ioo] at havg
  have hreal : 2 * Real.pi * ‖F z‖ ^ 2 ≤
      ∫ θ in Ioo (-Real.pi) Real.pi, ‖F (circleMap z a θ)‖ ^ 2 ∂volume := by
    calc
      _ ≤ 2 * Real.pi * Real.circleAverage (fun w => ‖F w‖ ^ 2) z a :=
        mul_le_mul_of_nonneg_left (holomorphic_circle_norm_sq_mean F hF z a ha hball)
          (by positivity)
      _ = _ := by
        rw [havg]
        simp only [smul_eq_mul]
        field_simp
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal hreal

end Yau.Proofs.D03Aux
