import Yau.LeafProofs.L10GreenIntegral
import Yau.LeafProofs.L09

/-! The singularity in the gradient kernel has uniformly small local mass. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate ContDiff Topology

namespace Yau.LeafProofs

theorem discGreen_inverseNorm_integrable (r : ℝ) :
    IntegrableOn (fun x : ℂ => ‖x‖⁻¹) (Metric.ball 0 r) volume := by
  rw [integrableOn_fun_norm_addHaar (volume : Measure ℂ)]
  simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul]
  apply (integrableOn_const (isCompact_Icc.measure_lt_top.ne) :
    IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 r) volume).mono_set
      Set.Ioo_subset_Icc_self |>.congr_fun
  · intro x hx
    exact (mul_inv_cancel₀ hx.1.ne').symm
  · exact measurableSet_Ioo

theorem discGreen_inverseNorm_mass {r : ℝ} (hr : 0 < r) :
    (∫ x in Metric.ball (0 : ℂ) r, ‖x‖⁻¹) = 2 * Real.pi * r := by
  let q : ℝ → ℝ := fun t => if t < r then t⁻¹ else 0
  have hrad := integral_fun_norm_addHaar (volume : Measure ℂ) q
  have hleft : (∫ x : ℂ, q ‖x‖) = ∫ x in Metric.ball (0 : ℂ) r, ‖x‖⁻¹ := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards with x
    simp [q, Set.indicator, Metric.mem_ball, dist_zero_right]
  have hright : (∫ t in Set.Ioi (0 : ℝ), t ^ (Module.finrank ℝ ℂ - 1) • q t) = r := by
    simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul]
    rw [← integral_indicator measurableSet_Ioi]
    calc
      _ = ∫ t in Set.Ioo (0 : ℝ) r, (1 : ℝ) := by
        rw [← integral_indicator measurableSet_Ioo]
        apply integral_congr_ae
        filter_upwards with t
        by_cases ht : 0 < t
        · by_cases htr : t < r
          · simp [q, Set.indicator, ht, htr, ht.ne']
          · simp [q, Set.indicator, ht, htr]
        · simp [Set.indicator, ht]
      _ = r := by simp [hr.le]
  rw [hleft, hright] at hrad
  simpa [Complex.finrank_real_complex, measureReal_def, Complex.volume_ball, hr.le, mul_assoc] using hrad

theorem discGreen_inverseNorm_integrable_ball (z : ℂ) (r : ℝ) :
    IntegrableOn (fun w : ℂ => ‖z - w‖⁻¹) (Metric.ball z r) volume := by
  have h := ((volume : Measure ℂ).measurePreserving_sub_left z).integrableOn_comp_preimage
    (MeasurableEquiv.subLeft z).measurableEmbedding |>.mpr (discGreen_inverseNorm_integrable r)
  simpa [Function.comp_def, Metric.ball, dist_eq_norm, norm_sub_rev] using h

theorem discGreen_inverseNorm_mass_ball (z : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ w in Metric.ball z r, ‖z - w‖⁻¹) = 2 * Real.pi * r := by
  have h := ((volume : Measure ℂ).measurePreserving_sub_left z).setIntegral_preimage_emb
    (MeasurableEquiv.subLeft z).measurableEmbedding (fun x : ℂ => ‖x‖⁻¹) (Metric.ball 0 r)
  have heq : (fun w : ℂ => z - w) ⁻¹' Metric.ball 0 r = Metric.ball z r := by
    ext w
    simp [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
  rw [heq] at h
  exact h.trans (discGreen_inverseNorm_mass hr)

theorem discGreen_inverseNorm_integrable_disc (z : ℂ) :
    IntegrableOn (fun w : ℂ => ‖z - w‖⁻¹) (Metric.ball (0 : ℂ) 1) volume :=
  (discGreen_inverseNorm_integrable_ball z (1 + dist 0 z)).mono_set
    (Metric.ball_subset_ball' le_rfl)

theorem discGreen_inverseNorm_near_mass (z : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ w in Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r, ‖z - w‖⁻¹) ≤
      2 * Real.pi * r := by
  rw [← discGreen_inverseNorm_mass_ball z hr]
  apply setIntegral_mono_set (discGreen_inverseNorm_integrable_ball z r)
    (Filter.Eventually.of_forall fun w => inv_nonneg.mpr (norm_nonneg _))
  exact Filter.Eventually.of_forall fun w hw => hw.2

theorem discGreen_gradient_continuousAt {z w : ℂ} (hzw : z ≠ w)
    (hden : 1 - z * conj w ≠ 0) :
    ContinuousAt (fun v => fderiv ℝ (fun y => discGreenKernel y v) z) w := by
  have hN : ContDiffAt ℝ 2 (fun p : ℂ × ℂ => p.2 - p.1) (w, z) := by fun_prop
  have hcj : ContDiffAt ℝ 2 (fun p : ℂ × ℂ => conj p.1) (w, z) :=
    Complex.conjCLE.contDiff.contDiffAt.comp (w, z) contDiffAt_fst
  have hC : ContDiffAt ℝ 2 (fun p : ℂ × ℂ => 1 - p.2 * conj p.1) (w, z) :=
    contDiffAt_const.sub (contDiffAt_snd.mul hcj)
  have hG : ContDiffAt ℝ 2
      (Function.uncurry (fun v y : ℂ => discGreenKernel y v)) (w, z) := by
    apply ContDiffAt.mul contDiffAt_const
    exact ((hN.norm ℂ (sub_ne_zero.mpr hzw)).log
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzw))).sub
      ((hC.norm ℂ hden).log (norm_ne_zero_iff.mpr hden))
  have hD : ContDiffAt ℝ 1 (fun v => fderiv ℝ (fun y => discGreenKernel y v) z) w :=
    hG.fderiv contDiffAt_const (by norm_num)
  exact hD.continuousAt

theorem discGreen_gradient_aestronglyMeasurable {z : ℂ} (hz : ‖z‖ ≤ 1) :
    AEStronglyMeasurable (fun w => fderiv ℝ (fun y => discGreenKernel y w) z)
      (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
  have hc : ContinuousOn (fun w => fderiv ℝ (fun y => discGreenKernel y w) z)
      (Metric.ball (0 : ℂ) 1 \ {z}) := by
    intro w hw
    apply ContinuousAt.continuousWithinAt
    exact discGreen_gradient_continuousAt
      (by simpa only [Set.mem_singleton_iff] using Ne.symm hw.2)
      (discGreen_denominator_ne_zero hz (by simpa using hw.1))
  have hm := hc.aestronglyMeasurable (μ := (volume : Measure ℂ))
    (measurableSet_ball.diff (measurableSet_singleton z))
  have hset : Metric.ball (0 : ℂ) 1 \ {z} =ᵐ[volume] Metric.ball (0 : ℂ) 1 := by
    filter_upwards [(volume : Measure ℂ).ae_ne z] with w hw
    simp [hw]
  rwa [Measure.restrict_congr_set hset] at hm

theorem discGreen_gradient_integrable {z : ℂ} (hz : ‖z‖ ≤ 1) :
    IntegrableOn (fun w => fderiv ℝ (fun y => discGreenKernel y w) z)
      (Metric.ball (0 : ℂ) 1) volume := by
  apply ((discGreen_inverseNorm_integrable_disc z).const_mul Real.pi⁻¹).mono'
    (discGreen_gradient_aestronglyMeasurable hz)
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae ((volume : Measure ℂ).ae_ne z)] with w hw hne
  exact discGreen_gradient_bound hz (by simpa using hw) hne.symm

theorem discGreen_gradient_near_mass {z : ℂ} (hz : ‖z‖ ≤ 1) {r : ℝ} (hr : 0 < r) :
    (∫ w in Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r,
      ‖fderiv ℝ (fun y => discGreenKernel y w) z‖) ≤ 2 * r := by
  have hInv : IntegrableOn (fun w : ℂ => ‖z - w‖⁻¹)
      (Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r) volume :=
    (discGreen_inverseNorm_integrable_disc z).mono_set Set.inter_subset_left
  have hGrad : IntegrableOn (fun w => ‖fderiv ℝ (fun y => discGreenKernel y w) z‖)
      (Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r) volume :=
    ((discGreen_gradient_integrable hz).mono_set Set.inter_subset_left).norm
  calc
    _ ≤ ∫ w in Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r, Real.pi⁻¹ * ‖z - w‖⁻¹ := by
      apply integral_mono_ae hGrad (hInv.const_mul _)
      filter_upwards [ae_restrict_mem (measurableSet_ball.inter measurableSet_ball),
        ae_restrict_of_ae ((volume : Measure ℂ).ae_ne z)] with w hw hne
      exact discGreen_gradient_bound hz (by simpa using hw.1) hne.symm
    _ = Real.pi⁻¹ * (∫ w in Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r, ‖z - w‖⁻¹) :=
      integral_const_mul _ _
    _ ≤ Real.pi⁻¹ * (2 * Real.pi * r) :=
      mul_le_mul_of_nonneg_left (discGreen_inverseNorm_near_mass z hr) (by positivity)
    _ = 2 * r := by field_simp

end Yau.LeafProofs
