import Yau.LeafProofs.L10DiscGradientMeasure

/-! Fubini and the one-dimensional fundamental theorem of calculus
identify the actual Green solution along every affine path in the closed disc. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff ComplexConjugate

namespace Yau.LeafProofs

theorem discGreenSolution_affine_FTC {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1))
    (x v : ℂ) (a b : ℝ)
    (hpath : ∀ t ∈ Set.uIcc a b, x + t • v ∈ Metric.closedBall (0 : ℂ) 1) :
    discGreenSolution f (x + b • v) - discGreenSolution f (x + a • v) =
      ∫ t in a..b, discGreenDerivative f (x + t • v) v := by
  have hJoint := discGreen_jointDir_affine_integrable hf x v a b hpath
  have hFTC : (fun w => ∫ t in a..b, discGreenJointDir v (x + t • v) w • f w) =ᵐ[
      (volume : Measure ℂ).restrict (Metric.ball (0 : ℂ) 1)]
      (fun w => discGreenKernel (x + b • v) w • f w - discGreenKernel (x + a • v) w • f w) := by
    filter_upwards [hJoint.prod_left_ae, ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (ae_not_on_complex_affine_line x v)] with w hint hw hline
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (intervalIntegrable_iff.mpr hint)
    intro t ht
    have hden := discGreen_denominator_ne_zero
      (show ‖x + t • v‖ ≤ 1 by simpa using hpath t ht) (show ‖w‖ < 1 by simpa using hw)
    have hG := discGreen_joint_differentiableAt (hline t).symm hden
    have hcurve : HasDerivAt (fun t : ℝ => (x + t • v, w)) (v, 0) t := by
      simpa using ((((hasDerivAt_id t).smul_const v).const_add x).prodMk
        (hasDerivAt_const t w))
    have hd : HasDerivAt (fun s : ℝ => discGreenKernel (x + s • v) w)
        (discGreenJointDir v (x + t • v) w) t := by
      simpa only [Function.comp_def, discGreenJointDir, discGreenJoint] using
        hG.hasFDerivAt.comp_hasDerivAt t hcurve
    exact hd.smul_const (f w)
  calc
    _ = ∫ w in Metric.ball (0 : ℂ) 1,
        discGreenKernel (x + b • v) w • f w - discGreenKernel (x + a • v) w • f w := by
      rw [integral_sub
        (discGreen_solution_integrable hf (hpath b Set.right_mem_uIcc))
        (discGreen_solution_integrable hf (hpath a Set.left_mem_uIcc))]
      rfl
    _ = ∫ w in Metric.ball (0 : ℂ) 1,
        ∫ t in a..b, discGreenJointDir v (x + t • v) w • f w :=
      (integral_congr_ae hFTC).symm
    _ = ∫ t in a..b, ∫ w in Metric.ball (0 : ℂ) 1,
        discGreenJointDir v (x + t • v) w • f w := (intervalIntegral_integral_swap hJoint).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact (discGreen_jointDir_weighted_integral hf (by simpa using hpath t ht) v).2

theorem discGreenSolution_hasDerivAt_affine {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) (v : ℂ) :
    HasDerivAt (fun t : ℝ => discGreenSolution f (z + t • v))
      (discGreenDerivative f z v) 0 := by
  let O : Set ℝ := (fun t : ℝ => z + t • v) ⁻¹' Metric.ball (0 : ℂ) 1
  have hcurve : Continuous (fun t : ℝ => z + t • v) := by fun_prop
  have hO : IsOpen O := Metric.isOpen_ball.preimage hcurve
  have hzO : (0 : ℝ) ∈ O := by simpa [O] using hz
  let q : ℝ → ℂ := fun t => discGreenDerivative f (z + t • v) v
  have hqc : ContinuousOn q O := by
    have hD := (discGreenDerivative_continuousOn hf).comp hcurve.continuousOn
      (show Set.MapsTo (fun t : ℝ => z + t • v) O (Metric.closedBall (0 : ℂ) 1) by
        intro t ht; exact Metric.ball_subset_closedBall ht)
    exact hD.clm_apply continuousOn_const
  have hq0 : ContinuousAt q 0 := hqc.continuousAt (hO.mem_nhds hzO)
  have hprim : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, q s) (q 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right (by simp)
      (hqc.stronglyMeasurableAtFilter hO 0 hzO) hq0
  have heq : (fun t : ℝ => discGreenSolution f (z + t • v)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => discGreenSolution f z + ∫ s in (0 : ℝ)..t, q s) := by
    obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.mp hO 0 hzO
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    have hpath : ∀ s ∈ Set.uIcc (0 : ℝ) t, z + s • v ∈ Metric.closedBall (0 : ℂ) 1 := by
      intro s hs
      apply Metric.ball_subset_closedBall
      apply hδO
      have hst : |s| ≤ |t| := by
        rw [Set.mem_uIcc] at hs
        rcases hs with hs | hs
        · rw [abs_of_nonneg hs.1, abs_of_nonneg (hs.1.trans hs.2)]
          exact hs.2
        · rw [abs_of_nonpos hs.2, abs_of_nonpos (hs.1.trans hs.2)]
          linarith [hs.1]
      have ht' : |t| < δ := by simpa [Real.dist_eq] using ht
      simpa [Real.dist_eq] using hst.trans_lt ht'
    have hF := discGreenSolution_affine_FTC hf z v 0 t hpath
    simpa only [zero_smul, add_zero, q, add_comm] using (eq_add_of_sub_eq hF)
  have hd := hprim.const_add (discGreenSolution f z)
  have hfinal := hd.congr_of_eventuallyEq heq
  simpa [q] using hfinal

end Yau.LeafProofs
