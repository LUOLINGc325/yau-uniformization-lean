import Yau.Proofs.V02DiscTrace

/-! The genuine nonholomorphic W¹,² to L² plus H¹/² trace bound, followed
by its application to the same canonical Green dbar solution. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint Yau.LeafProofs

theorem complex_disc_trace_L2_bound {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    (∫ θ in (-Real.pi)..Real.pi, ‖u (L08_unitCircle θ)‖ ^ 2) ≤
      3 * (∫ z in Metric.ball (0 : ℂ) 1, ‖u z‖ ^ 2) +
        ∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq u z := by
  have hur : ContDiffOn ℝ ∞ (fun z => (u z).re) (Metric.closedBall (0 : ℂ) 1) :=
    Complex.reCLM.contDiff.comp_contDiffOn hu
  have hui : ContDiffOn ℝ ∞ (fun z => (u z).im) (Metric.closedBall (0 : ℂ) 1) :=
    Complex.imCLM.contDiff.comp_contDiffOn hu
  have hc : Continuous (fun θ => u (L08_unitCircle θ)) :=
    hu.continuousOn.comp_continuous L08_continuous_unitCircle
      (fun θ => by simp [Metric.mem_closedBall, dist_zero_right, L08_norm_unitCircle])
  have hcr : IntervalIntegrable (fun θ => (u (L08_unitCircle θ)).re ^ 2) volume (-Real.pi) Real.pi :=
    (Complex.continuous_re.comp hc).pow 2 |>.intervalIntegrable (-Real.pi) Real.pi
  have hci : IntervalIntegrable (fun θ => (u (L08_unitCircle θ)).im ^ 2) volume (-Real.pi) Real.pi :=
    (Complex.continuous_im.comp hc).pow 2 |>.intervalIntegrable (-Real.pi) Real.pi
  have hUr : IntegrableOn (fun z => (u z).re ^ 2) (Metric.ball (0 : ℂ) 1) :=
    discEnergy_integrableOn (hur.continuousOn.pow 2)
  have hUi : IntegrableOn (fun z => (u z).im ^ 2) (Metric.ball (0 : ℂ) 1) :=
    discEnergy_integrableOn (hui.continuousOn.pow 2)
  have hGr := discEnergy_integrableOn (discEnergyRealGradientSq_continuousOn hur)
  have hGi := discEnergy_integrableOn (discEnergyRealGradientSq_continuousOn hui)
  have hboundary : (∫ θ in (-Real.pi)..Real.pi, ‖u (L08_unitCircle θ)‖ ^ 2) =
      (∫ θ in (-Real.pi)..Real.pi, (u (L08_unitCircle θ)).re ^ 2) +
        ∫ θ in (-Real.pi)..Real.pi, (u (L08_unitCircle θ)).im ^ 2 := by
    simp_rw [discEnergy_norm_sq_re_im]
    exact intervalIntegral.integral_add hcr hci
  have hnorm : (∫ z in Metric.ball (0 : ℂ) 1, ‖u z‖ ^ 2) =
      (∫ z in Metric.ball (0 : ℂ) 1, (u z).re ^ 2) +
        ∫ z in Metric.ball (0 : ℂ) 1, (u z).im ^ 2 := by
    simp_rw [discEnergy_norm_sq_re_im]
    exact integral_add hUr hUi
  have hgrad : (∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq u z) =
      (∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealGradientSq (fun w => (u w).re) z) +
        (∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealGradientSq (fun w => (u w).im) z) := by
    calc
      _ = ∫ z in Metric.ball (0 : ℂ) 1,
          discEnergyRealGradientSq (fun w => (u w).re) z +
            discEnergyRealGradientSq (fun w => (u w).im) z :=
        setIntegral_congr_fun Metric.isOpen_ball.measurableSet (fun z hz =>
          discEnergyGradientSq_re_im hu (Metric.ball_subset_closedBall hz))
      _ = _ := integral_add hGr hGi
  rw [hboundary, hnorm, hgrad]
  have hr := real_disc_trace_L2_bound hur
  have hi := real_disc_trace_L2_bound hui
  linarith

theorem complex_disc_circleL2_bound {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    circleAverage (fun θ => ‖u (circlePoint θ)‖ ^ 2) ≤ (2 * Real.pi)⁻¹ *
      (3 * (∫ z in Metric.ball (0 : ℂ) 1, ‖u z‖ ^ 2) +
        ∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq u z) := by
  have hp := V03Proof.circleTrace_periodic (fun z => ‖u z‖ ^ 2)
  have hs := hp.intervalIntegral_add_eq (-Real.pi) 0
  have he : -Real.pi + 2 * Real.pi = Real.pi := by ring
  simp only [he, zero_add] at hs
  unfold circleAverage
  rw [← hs]
  exact mul_le_mul_of_nonneg_left (complex_disc_trace_L2_bound hu) (by positivity)

theorem nonholomorphicDiscTraceEstimate :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ → ℂ,
      ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1) →
      ENNReal.ofReal (circleAverage (fun θ => ‖u (circlePoint θ)‖ ^ 2)) +
        boundaryDSq (fun θ (_ : Unit) => u (circlePoint θ)) ≤
        ENNReal.ofReal (C * ((∫ z in Metric.ball (0 : ℂ) 1, ‖u z‖ ^ 2) +
          ∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq u z)) := by
  let C := 3 * (2 * Real.pi)⁻¹ + Real.pi⁻¹
  refine ⟨C, by dsimp [C]; positivity, fun u hu => ?_⟩
  have hU : 0 ≤ ∫ z in Metric.ball (0 : ℂ) 1, ‖u z‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hG : 0 ≤ ∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq u z :=
    integral_nonneg fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    _ ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹ *
          (3 * (∫ z in Metric.ball (0 : ℂ) 1, ‖u z‖ ^ 2) +
            ∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq u z)) +
        ENNReal.ofReal (Real.pi⁻¹ * ∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq u z) :=
      add_le_add (ENNReal.ofReal_le_ofReal (complex_disc_circleL2_bound hu))
        (complex_disc_Hhalf_bound hu)
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ *
          (3 * (∫ z in Metric.ball (0 : ℂ) 1, ‖u z‖ ^ 2) +
            ∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq u z) +
        Real.pi⁻¹ * ∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq u z) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      dsimp only [C]
      nlinarith [mul_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹) hG,
        mul_nonneg (by positivity : 0 ≤ Real.pi⁻¹) hU])

/-- One fixed-disc constant controls the nonholomorphic Q trace for every
smooth density. No solution operator or trace estimate is supplied as input. -/
theorem canonicalDbar_boundaryTraceEstimate :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℂ → ℂ,
      ContDiffOn ℝ ∞ b (Metric.closedBall (0 : ℂ) 1) →
      ENNReal.ofReal (circleAverage (fun θ => ‖discDbarSolution b (circlePoint θ)‖ ^ 2)) +
        boundaryDSq (fun θ (_ : Unit) => discDbarSolution b (circlePoint θ)) ≤
        ENNReal.ofReal (C * ∫ z in Metric.ball (0 : ℂ) 1, ‖b z‖ ^ 2) := by
  obtain ⟨C, hC, htrace⟩ := nonholomorphicDiscTraceEstimate
  refine ⟨16 * C, by positivity, fun b hb => ?_⟩
  apply (htrace (discDbarSolution b) (discDbarSolution_contDiffOn hb)).trans
  apply ENNReal.ofReal_le_ofReal
  have he := mul_le_mul_of_nonneg_left (discDbarSolution_W12_estimate hb) hC.le
  nlinarith

end Yau.Blueprint.V02Proof
