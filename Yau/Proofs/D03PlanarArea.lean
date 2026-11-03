import Yau.Proofs.D03PlanarPolar

open scoped Topology RealInnerProductSpace ENNReal
open MeasureTheory Set Filter Metric

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau

private theorem lintegral_radius (a : ℝ) (ha : 0 < a) :
    (∫⁻ r in Ioo (0 : ℝ) a, ENNReal.ofReal r ∂volume) = ENNReal.ofReal (a ^ 2 / 2) := by
  have hint : IntegrableOn (fun r : ℝ => r) (Ioo (0 : ℝ) a) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).1 (continuous_id.intervalIntegrable _ _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha.le, integral_id]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hr.1.le

/-- The ordinary Euclidean area submean inequality on a holomorphic closed disc. -/
theorem holomorphic_area_mean {q : ℕ} (F : ℂ → ComplexVector q) {U : Set ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (z : ℂ) (a : ℝ) (ha : 0 < a)
    (hball : closedBall z a ⊆ U) :
    ENNReal.ofReal (Real.pi * a ^ 2 * ‖F z‖ ^ 2) ≤
      ∫⁻ w in ball z a, ENNReal.ofReal (‖F w‖ ^ 2) ∂(volume : Measure ℂ) := by
  let S : Set (ℝ × ℝ) := Ioo 0 a ×ˢ Ioo (-Real.pi) Real.pi
  let P : ℝ × ℝ → ℂ := fun p => z + Complex.polarCoord.symm p
  let f : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (p.1 * ‖F (P p)‖ ^ 2)
  let g : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (‖F w‖ ^ 2)
  have hP : Continuous P := by
    dsimp [P]
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hdist (p : ℝ × ℝ) : dist (P p) z = |p.1| := by
    simp only [P, dist_eq_norm, add_sub_cancel_left, Complex.norm_polarCoord_symm]
  have hmap : MapsTo P S U := by
    intro p hp
    apply hball
    rw [mem_closedBall, hdist, abs_of_pos hp.1.1]
    exact hp.1.2.le
  have hfc : ContinuousOn f S :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (continuous_fst.continuousOn.mul ((hF.continuousOn.comp hP.continuousOn hmap).norm.pow 2))
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hT : S ⊆ Complex.polarCoord.target := by
    intro p hp
    rw [Complex.polarCoord_target]
    exact ⟨hp.1.1, hp.2⟩
  have hcircle (p : ℝ × ℝ) : P p = circleMap z p.1 p.2 := by
    simp only [P, Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
    push_cast
    ring
  have hArea : (∫⁻ p in Complex.polarCoord.target,
      ENNReal.ofReal p.1 * (ball z a).indicator g (P p) ∂volume) =
      ∫⁻ w in ball z a, g w ∂volume := by
    calc
      _ = ∫⁻ w : ℂ, (ball z a).indicator g (z + w) ∂volume := by
        simpa only [P, smul_eq_mul, Complex.polarCoord_target, polarCoord_target] using
          Complex.lintegral_comp_polarCoord_symm (fun w => (ball z a).indicator g (z + w))
      _ = ∫⁻ w : ℂ, (ball z a).indicator g w ∂volume := lintegral_add_left_eq_self _ z
      _ = _ := lintegral_indicator measurableSet_ball g
  calc
    _ = (∫⁻ r in Ioo (0 : ℝ) a, ENNReal.ofReal r ∂volume) *
        ENNReal.ofReal (2 * Real.pi * ‖F z‖ ^ 2) := by
      rw [lintegral_radius a ha, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ = ∫⁻ r in Ioo (0 : ℝ) a,
        ENNReal.ofReal r * ENNReal.ofReal (2 * Real.pi * ‖F z‖ ^ 2) ∂volume := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ r in Ioo (0 : ℝ) a, ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (r, θ) ∂volume ∂volume := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro r hr
      have hinner := holomorphic_circle_lintegral_lower F hF z r hr.1
        ((closedBall_subset_closedBall hr.2.le).trans hball)
      calc
        _ ≤ ENNReal.ofReal r * ∫⁻ θ in Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal (‖F (circleMap z r θ)‖ ^ 2) ∂volume :=
          by gcongr
        _ = _ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          apply lintegral_congr
          intro θ
          dsimp [f]
          rw [hcircle, ENNReal.ofReal_mul hr.1.le]
    _ = ∫⁻ p in S, f p ∂volume := by
      symm
      exact setLIntegral_prod f (hfc.aemeasurable hS)
    _ = ∫⁻ p in S, ENNReal.ofReal p.1 * (ball z a).indicator g (P p) ∂volume := by
      apply setLIntegral_congr_fun hS
      intro p hp
      have hmem : P p ∈ ball z a := by
        rw [mem_ball, hdist, abs_of_pos hp.1.1]
        exact hp.1.2
      change ENNReal.ofReal (p.1 * ‖F (P p)‖ ^ 2) =
        ENNReal.ofReal p.1 * (ball z a).indicator g (P p)
      rw [Set.indicator_of_mem hmem]
      exact ENNReal.ofReal_mul hp.1.1.le
    _ ≤ ∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 * (ball z a).indicator g (P p) ∂volume := lintegral_mono_set hT
    _ = _ := hArea

end Yau.Proofs.D03Aux
