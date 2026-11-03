import Yau.LeafProofs.L10DiscBoundaryBridge

/-! A joint measurable derivative representative and its genuine L¹
bounds on affine parameter paths. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff ComplexConjugate

namespace Yau.LeafProofs

/-- The literal two-variable kernel. -/
def discGreenJoint (p : ℂ × ℂ) : ℝ := discGreenKernel p.1 p.2

/-- A globally Borel representative for the derivative in the first variable. -/
def discGreenJointDir (v z w : ℂ) : ℝ :=
  fderiv ℝ discGreenJoint (z, w) (v, 0)

theorem discGreen_joint_differentiableAt {z w : ℂ}
    (hzw : z ≠ w) (hden : 1 - z * conj w ≠ 0) :
    DifferentiableAt ℝ discGreenJoint (z, w) := by
  have hN : ContDiffAt ℝ 2 (fun p : ℂ × ℂ => p.1 - p.2) (z, w) := by fun_prop
  have hcj : ContDiffAt ℝ 2 (fun p : ℂ × ℂ => conj p.2) (z, w) :=
    Complex.conjCLE.contDiff.contDiffAt.comp (z, w) contDiffAt_snd
  have hC : ContDiffAt ℝ 2 (fun p : ℂ × ℂ => 1 - p.1 * conj p.2) (z, w) :=
    contDiffAt_const.sub (contDiffAt_fst.mul hcj)
  have hG : ContDiffAt ℝ 2 discGreenJoint (z, w) := by
    apply ContDiffAt.mul contDiffAt_const
    exact ((hN.norm ℂ (sub_ne_zero.mpr hzw)).log
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzw))).sub
      ((hC.norm ℂ hden).log (norm_ne_zero_iff.mpr hden))
  exact hG.differentiableAt (by norm_num)

theorem discGreen_jointDir_eq {z w : ℂ}
    (hzw : z ≠ w) (hden : 1 - z * conj w ≠ 0) (v : ℂ) :
    discGreenJointDir v z w = fderiv ℝ (fun y => discGreenKernel y w) z v := by
  have hi : HasFDerivAt (fun y : ℂ => (y, w)) (ContinuousLinearMap.inl ℝ ℂ ℂ) z := by
    simpa using (ContinuousLinearMap.inl ℝ ℂ ℂ).hasFDerivAt.add_const (0, w)
  have hd : HasFDerivAt (fun y => discGreenKernel y w)
      ((fderiv ℝ discGreenJoint (z, w)).comp (ContinuousLinearMap.inl ℝ ℂ ℂ)) z := by
    simpa only [Function.comp_def, discGreenJoint] using
      (discGreen_joint_differentiableAt hzw hden).hasFDerivAt.comp z hi
  exact congrArg (fun L : ℂ →L[ℝ] ℝ => L v) hd.fderiv.symm

theorem discGreen_jointDir_measurable (v : ℂ) :
    Measurable (fun p : ℂ × ℂ => discGreenJointDir v p.1 p.2) := by
  exact measurable_fderiv_apply_const ℝ discGreenJoint (v, 0)

theorem discGreen_jointDir_weighted_ae {f : ℂ → ℂ} {z : ℂ}
    (hz : ‖z‖ ≤ 1) (v : ℂ) :
    (fun w => discGreenJointDir v z w • f w) =ᵐ[
      (volume : Measure ℂ).restrict (Metric.ball (0 : ℂ) 1)]
      (fun w => discGreenDerivativeIntegrand f z w v) := by
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae ((volume : Measure ℂ).ae_ne z)] with w hw hne
  rw [discGreen_jointDir_eq hne.symm
    (discGreen_denominator_ne_zero hz (by simpa using hw))]
  rfl

theorem discGreen_jointDir_weighted_integral {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : ‖z‖ ≤ 1) (v : ℂ) :
    IntegrableOn (fun w => discGreenJointDir v z w • f w)
      (Metric.ball (0 : ℂ) 1) volume ∧
    (∫ w in Metric.ball (0 : ℂ) 1, discGreenJointDir v z w • f w) =
      discGreenDerivative f z v := by
  have heval : IntegrableOn (fun w => discGreenDerivativeIntegrand f z w v)
      (Metric.ball (0 : ℂ) 1) volume :=
    (ContinuousLinearMap.apply ℝ ℂ v).integrable_comp
      (discGreenDerivativeIntegrand_integrable hf hz)
  refine ⟨heval.congr (discGreen_jointDir_weighted_ae hz v).symm, ?_⟩
  exact (integral_congr_ae (discGreen_jointDir_weighted_ae hz v)).trans
    (ContinuousLinearMap.integral_apply (discGreenDerivativeIntegrand_integrable hf hz) v).symm

theorem discGreenDerivativeIntegrand_mass {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ‖f w‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∫ w in Metric.ball (0 : ℂ) 1, ‖discGreenDerivativeIntegrand f z w‖) ≤ 6 * M := by
  have hsubset : Metric.ball (0 : ℂ) 1 ⊆ Metric.ball z 3 := by
    intro w hw
    have hwN : ‖w‖ < 1 := by simpa using hw
    have ht := norm_sub_le w z
    simp only [Metric.mem_ball, dist_eq_norm]
    linarith
  have hi := discGreenDerivativeIntegrand_near_mass hf hM hbound hz (by norm_num : (0 : ℝ) < 3)
  rw [Set.inter_eq_left.mpr hsubset] at hi
  nlinarith

theorem discGreen_jointDir_weighted_mass {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ‖f w‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (v : ℂ) :
    (∫ w in Metric.ball (0 : ℂ) 1, ‖discGreenJointDir v z w • f w‖) ≤ 6 * M * ‖v‖ := by
  have hi := discGreenDerivativeIntegrand_integrable hf hz
  calc
    _ = ∫ w in Metric.ball (0 : ℂ) 1, ‖discGreenDerivativeIntegrand f z w v‖ :=
      integral_congr_ae ((discGreen_jointDir_weighted_ae hz v).fun_comp norm)
    _ ≤ ∫ w in Metric.ball (0 : ℂ) 1, ‖discGreenDerivativeIntegrand f z w‖ * ‖v‖ := by
      apply integral_mono_ae ((ContinuousLinearMap.apply ℝ ℂ v).integrable_comp hi).norm
        (hi.norm.mul_const ‖v‖)
      exact Eventually.of_forall fun w => (discGreenDerivativeIntegrand f z w).le_opNorm v
    _ = (∫ w in Metric.ball (0 : ℂ) 1, ‖discGreenDerivativeIntegrand f z w‖) * ‖v‖ :=
      integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (discGreenDerivativeIntegrand_mass hf hM hbound hz) (norm_nonneg _)

/-- A real affine line in the complex plane has zero area. The good set
is common to every real path parameter, including an uncountable interval. -/
theorem ae_not_on_complex_affine_line (x v : ℂ) :
    ∀ᵐ w ∂(volume : Measure ℂ), ∀ t : ℝ, w ≠ x + t • v := by
  by_cases hv : v = 0
  · simpa [hv] using ((volume : Measure ℂ).ae_ne x)
  let S : Submodule ℝ ℂ := Submodule.span ℝ {v}
  have hproper : S ≠ ⊤ := by
    intro htop
    have hdim : Module.finrank ℝ S = 1 := finrank_span_singleton hv
    rw [htop, finrank_top, Complex.finrank_real_complex] at hdim
    norm_num at hdim
  have hzero : volume ((fun w : ℂ => w + -x) ⁻¹' (S : Set ℂ)) = 0 := by
    rw [measure_preimage_add_right, Measure.addHaar_submodule volume S hproper]
  have hgood : ∀ᵐ w ∂(volume : Measure ℂ), w ∉ (fun w : ℂ => w + -x) ⁻¹' (S : Set ℂ) :=
    by
      apply ae_iff.mpr
      rw [show {w | ¬ w ∉ (fun w : ℂ => w + -x) ⁻¹' (S : Set ℂ)} =
          (fun w : ℂ => w + -x) ⁻¹' (S : Set ℂ) by ext w; simp]
      exact hzero
  filter_upwards [hgood] with w hw
  intro t hwt
  apply hw
  change w + -x ∈ S
  rw [hwt]
  simpa using S.smul_mem t (Submodule.subset_span (by simp : v ∈ ({v} : Set ℂ)))

theorem discGreen_jointDir_affine_integrable {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1))
    (x v : ℂ) (a b : ℝ)
    (hpath : ∀ t ∈ Set.uIcc a b, x + t • v ∈ Metric.closedBall (0 : ℂ) 1) :
    Integrable (fun p : ℝ × ℂ => discGreenJointDir v (x + p.1 • v) p.2 • f p.2)
      (((volume : Measure ℝ).restrict (Set.uIoc a b)).prod
        ((volume : Measure ℂ).restrict (Metric.ball (0 : ℂ) 1))) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℂ => discGreenJointDir v (x + p.1 • v) p.2 • f p.2)
      (((volume : Measure ℝ).restrict (Set.uIoc a b)).prod
        ((volume : Measure ℂ).restrict (Metric.ball (0 : ℂ) 1))) := by
    have hm : Measurable (fun p : ℝ × ℂ => discGreenJointDir v (x + p.1 • v) p.2) :=
      (discGreen_jointDir_measurable v).comp (show Measurable (fun p : ℝ × ℂ => (x + p.1 • v, p.2)) by fun_prop)
    exact hm.aestronglyMeasurable.smul
      ((hf.mono Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball).comp_snd
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    exact (discGreen_jointDir_weighted_integral hf
      (by simpa using hpath t (Set.uIoc_subset_uIcc ht)) v).1
  · obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf
    have hMpos : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0 (by simp))
    apply (integrableOn_const (isCompact_uIcc.measure_lt_top.ne) :
      IntegrableOn (fun _ : ℝ => 6 * M * ‖v‖) (Set.uIcc a b) volume).mono_set
        Set.uIoc_subset_uIcc |>.mono' hmeas.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Real.norm_of_nonneg (integral_nonneg fun w => norm_nonneg _)]
    exact discGreen_jointDir_weighted_mass hf hMpos hM
      (by simpa using hpath t (Set.uIoc_subset_uIcc ht)) v

end Yau.LeafProofs
