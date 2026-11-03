import Yau.LeafProofs.L10DiscEnergyNorm

/-! Exact conversion from the two real Hessian energies to the complex
Hessian energy, followed by the original square-root norm estimate. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace Yau.LeafProofs

def discEnergyRealHessianSq (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  (discEnergyPartial (discEnergyPartial u 1) 1 z)^2 +
  (discEnergyPartial (discEnergyPartial u 1) Complex.I z)^2 +
  (discEnergyPartial (discEnergyPartial u Complex.I) 1 z)^2 +
  (discEnergyPartial (discEnergyPartial u Complex.I) Complex.I z)^2

theorem discEnergyRealHessianSq_continuousOn {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    ContinuousOn (discEnergyRealHessianSq u) (Metric.closedBall (0 : ℂ) 1) := by
  have hc (v w : ℂ) : ContinuousOn (fun z => (discEnergyPartial (discEnergyPartial u v) w z)^2)
      (Metric.closedBall (0 : ℂ) 1) :=
    ((discEnergyPartial_contDiffOn (discEnergyPartial_contDiffOn hu v) w).continuousOn.pow 2)
  exact (((hc 1 1).add (hc 1 Complex.I)).add (hc Complex.I 1)).add (hc Complex.I Complex.I)

theorem discEnergyHessianSq_re_im {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discEnergyHessianSq u z =
      discEnergyRealHessianSq (fun w => (u w).re) z +
      discEnergyRealHessianSq (fun w => (u w).im) z := by
  have hr (v w : ℂ) := discEnergyPartial_twice_clm Complex.reCLM hu v w hz
  have hi (v w : ℂ) := discEnergyPartial_twice_clm Complex.imCLM hu v w hz
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hr hi
  simp only [discEnergyHessianSq, discEnergyRealHessianSq, hr, hi, discEnergy_norm_sq_re_im]
  ring

/-- The two actual scalar Hessian inequalities combine into the complex one. -/
theorem discEnergy_complex_hessian_estimate {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (hr : (∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealHessianSq (fun w => (u w).re) z) ≤
      ∫ z in Metric.ball (0 : ℂ) 1, (discEnergyRealLaplacian (fun w => (u w).re) z)^2)
    (hi : (∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealHessianSq (fun w => (u w).im) z) ≤
      ∫ z in Metric.ball (0 : ℂ) 1, (discEnergyRealLaplacian (fun w => (u w).im) z)^2) :
    (∫ z in Metric.ball (0 : ℂ) 1, discEnergyHessianSq u z) ≤
      ∫ z in Metric.ball (0 : ℂ) 1, ‖discEnergyLaplacian u z‖^2 := by
  have hur : ContDiffOn ℝ ∞ (fun w => (u w).re) (Metric.closedBall (0 : ℂ) 1) :=
    Complex.reCLM.contDiff.comp_contDiffOn hu
  have hui : ContDiffOn ℝ ∞ (fun w => (u w).im) (Metric.closedBall (0 : ℂ) 1) :=
    Complex.imCLM.contDiff.comp_contDiffOn hu
  have hFr : IntegrableOn (fun z => (discEnergyRealLaplacian (fun w => (u w).re) z)^2)
      (Metric.ball (0 : ℂ) 1) :=
    discEnergy_integrableOn ((discEnergyRealLaplacian_continuousOn hur).pow 2)
  have hFi : IntegrableOn (fun z => (discEnergyRealLaplacian (fun w => (u w).im) z)^2)
      (Metric.ball (0 : ℂ) 1) :=
    discEnergy_integrableOn ((discEnergyRealLaplacian_continuousOn hui).pow 2)
  have hHr : IntegrableOn (fun z => discEnergyRealHessianSq (fun w => (u w).re) z)
      (Metric.ball (0 : ℂ) 1) :=
    discEnergy_integrableOn (discEnergyRealHessianSq_continuousOn hur)
  have hHi : IntegrableOn (fun z => discEnergyRealHessianSq (fun w => (u w).im) z)
      (Metric.ball (0 : ℂ) 1) :=
    discEnergy_integrableOn (discEnergyRealHessianSq_continuousOn hui)
  calc
    _ = ∫ z in Metric.ball (0 : ℂ) 1,
        discEnergyRealHessianSq (fun w => (u w).re) z +
          discEnergyRealHessianSq (fun w => (u w).im) z :=
      setIntegral_congr_fun Metric.isOpen_ball.measurableSet
        (fun z hz => discEnergyHessianSq_re_im hu (Metric.ball_subset_closedBall hz))
    _ = _ := integral_add hHr hHi
    _ ≤ _ := add_le_add hr hi
    _ = ∫ z in Metric.ball (0 : ℂ) 1,
        (discEnergyRealLaplacian (fun w => (u w).re) z)^2 +
          (discEnergyRealLaplacian (fun w => (u w).im) z)^2 := (integral_add hFr hFi).symm
    _ = _ := by
      apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro z hz
      dsimp only
      rw [(discEnergyLaplacian_re_im hu (Metric.ball_subset_closedBall hz)).1,
        (discEnergyLaplacian_re_im hu (Metric.ball_subset_closedBall hz)).2,
        discEnergy_norm_sq_re_im]

/-- Once the Hessian energy has been bounded, the three exact original
Fréchet norms give the fixed numerical constant two. -/
theorem discEnergy_original_estimate {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (hzero : ∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = 0)
    (hH : (∫ z in Metric.ball (0 : ℂ) 1, discEnergyHessianSq u z) ≤
      ∫ z in Metric.ball (0 : ℂ) 1, ‖discEnergyLaplacian u z‖^2) :
    Real.sqrt (∑ k ∈ Finset.range 3, ∫ z in Metric.ball (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ k u z‖^2) ≤
      2 * Real.sqrt (∫ z in Metric.ball (0 : ℂ) 1, ‖discEnergyLaplacian u z‖^2) := by
  have hE := discEnergy_complex_first_order hu hzero
  have hN := discEnergy_original_norm_le hu
  have hF : 0 ≤ ∫ z in Metric.ball (0 : ℂ) 1, ‖discEnergyLaplacian u z‖^2 :=
    integral_nonneg (fun z => sq_nonneg _)
  have hbound : (∑ k ∈ Finset.range 3, ∫ z in Metric.ball (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ k u z‖^2) ≤
        4 * (∫ z in Metric.ball (0 : ℂ) 1, ‖discEnergyLaplacian u z‖^2) := by
    linarith only [hE.1, hE.2, hN, hH, hF]
  calc
    _ ≤ Real.sqrt (4 * (∫ z in Metric.ball (0 : ℂ) 1, ‖discEnergyLaplacian u z‖^2)) :=
      Real.sqrt_le_sqrt hbound
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num

end Yau.LeafProofs
