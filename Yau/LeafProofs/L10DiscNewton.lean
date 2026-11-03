import Yau.LeafProofs.L10DiscKernel

/-! The Newton part needs only smoothness within the closed disc. In
particular, its density is allowed to jump when extended by zero. -/

noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate Topology ContDiff Laplacian

namespace Yau.LeafProofs

/-- The unnormalized real Newton integral over the unit disc. -/
def discNewtonReal (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  ∫ w in Metric.ball (0 : ℂ) 1, Real.log ‖z - w‖ * f w

private theorem discNewtonReal_density {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    let g := (Metric.ball (0 : ℂ) 1).indicator f
    ContDiffOn ℝ ∞ g (Metric.ball (0 : ℂ) 1) ∧
      Integrable g volume ∧ HasCompactSupport g ∧
      ∀ z : ℂ, Integrable (fun w => Real.log ‖z - w‖ * g w) volume := by
  dsimp only
  let g := (Metric.ball (0 : ℂ) 1).indicator f
  have hfc := hf.continuousOn
  have hfi : Integrable g volume :=
    (integrable_indicator_iff measurableSet_ball).2
      ((hfc.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set
        Metric.ball_subset_closedBall)
  have hfs : HasCompactSupport g := by
    apply (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_tsupport g)
    apply Metric.isClosed_closedBall.closure_subset_iff.mpr
    intro w hw
    by_contra hwb
    exact hw (Set.indicator_of_notMem
      (fun h => hwb (Metric.ball_subset_closedBall h)) f)
  refine ⟨?_, hfi, hfs, ?_⟩
  · apply (hf.mono Metric.ball_subset_closedBall).congr
    intro w hw
    exact Set.indicator_of_mem hw f
  · intro z
    have hi := (L08_integrableOn_log_norm_sub_disc z 0 1).mul_continuousOn_of_subset
      hfc measurableSet_ball (isCompact_closedBall (0 : ℂ) 1) Metric.ball_subset_closedBall
    have hInd := (integrable_indicator_iff measurableSet_ball).2 hi
    convert hInd using 1
    funext w
    exact (Set.indicator_mul_right (Metric.ball (0 : ℂ) 1)
      (fun w => Real.log ‖z - w‖) f).symm

private theorem discNewtonReal_eq (f : ℂ → ℝ) (z : ℂ) :
    discNewtonReal f z = ∫ w, Real.log ‖z - w‖ *
      (Metric.ball (0 : ℂ) 1).indicator f w := by
  rw [discNewtonReal, ← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  filter_upwards with w
  exact Set.indicator_mul_right (Metric.ball (0 : ℂ) 1) (fun w => Real.log ‖z - w‖) f

theorem discNewtonReal_contDiffOn {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (discNewtonReal f) (Metric.ball (0 : ℂ) 1) := by
  obtain ⟨hg, hgi, hgs, hkernel⟩ := discNewtonReal_density hf
  have heq : discNewtonReal f = fun z => ∫ w, Real.log ‖z - w‖ *
      (Metric.ball (0 : ℂ) 1).indicator f w := funext (discNewtonReal_eq f)
  rw [heq]
  exact L08_contDiffOn_logPotential Metric.isOpen_ball hg hgi hgs (fun z _ => hkernel z)

theorem discNewtonReal_laplacian {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    LeafCandidates.realPlanarLaplacian (discNewtonReal f) z = 2 * Real.pi * f z := by
  obtain ⟨hg, hgi, hgs, hkernel⟩ := discNewtonReal_density hf
  rw [L08_realPlanarLaplacian_congr_nhds
    (Filter.Eventually.of_forall (discNewtonReal_eq f)),
    L08_realPlanarLaplacian_logPotential Metric.isOpen_ball hg hgi hgs
      (fun z _ => hkernel z) hz]
  simp only [Set.indicator_of_mem hz]

/-- The frozen complex-valued operator is the usual real Laplacian. -/
theorem disc_planarLaplacian_eq_laplacian {u : ℂ → ℂ} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) :
    LeafCandidates.planarLaplacian u z = (Δ u) z := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [LeafCandidates.planarLaplacian,
    fderiv_clm_apply hdu (differentiableAt_const (1 : ℂ)),
    fderiv_clm_apply hdu (differentiableAt_const Complex.I)]
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply, ContinuousLinearMap.flip_apply]

/-- The original complex Newton integral, before multiplying by `(2π)⁻¹`. -/
def discNewtonPotential (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w in Metric.ball (0 : ℂ) 1, Real.log ‖z - w‖ • f w

theorem discNewtonPotential_eq_real_im {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) (z : ℂ) :
    discNewtonPotential f z = (discNewtonReal (fun w => (f w).re) z : ℂ) +
      Complex.I * (discNewtonReal (fun w => (f w).im) z : ℂ) := by
  have hi : IntegrableOn (fun w => Real.log ‖z - w‖ • f w)
      (Metric.ball (0 : ℂ) 1) volume := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf
    exact (L08_integrableOn_log_norm_sub_disc z 0 1).smul_bdd M
      ((hf.mono Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball)
      (by filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
          exact hM w (Metric.ball_subset_closedBall hw))
  have hr := Complex.reCLM.integral_comp_comm hi
  have him := Complex.imCLM.integral_comp_comm hi
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, mul_zero, zero_sub, zero_add]
  · simpa [discNewtonPotential, discNewtonReal] using hr.symm
  · simpa [discNewtonPotential, discNewtonReal] using him.symm

theorem discNewtonPotential_contDiffOn {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (discNewtonPotential f) (Metric.ball (0 : ℂ) 1) := by
  have hr := discNewtonReal_contDiffOn (Complex.reCLM.contDiff.comp_contDiffOn hf)
  have hi := discNewtonReal_contDiffOn (Complex.imCLM.contDiff.comp_contDiffOn hf)
  have h := (Complex.ofRealCLM.contDiff.comp_contDiffOn hr).add
    ((Complex.I • Complex.ofRealCLM).contDiff.comp_contDiffOn hi)
  exact h.congr (fun z _ => discNewtonPotential_eq_real_im hf.continuousOn z)

theorem discNewtonPotential_laplacian {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    LeafCandidates.planarLaplacian (discNewtonPotential f) z =
      (2 * Real.pi) • f z := by
  have hr := discNewtonReal_contDiffOn (Complex.reCLM.contDiff.comp_contDiffOn hf)
  have hi := discNewtonReal_contDiffOn (Complex.imCLM.contDiff.comp_contDiffOn hf)
  have hrz : ContDiffAt ℝ 2 (discNewtonReal (fun w => (f w).re)) z :=
    (hr.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).of_le (by simp)
  have hiz : ContDiffAt ℝ 2 (discNewtonReal (fun w => (f w).im)) z :=
    (hi.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).of_le (by simp)
  rw [disc_planarLaplacian_eq_laplacian
    (((discNewtonPotential_contDiffOn hf).contDiffAt
      (Metric.isOpen_ball.mem_nhds hz)).of_le (by simp))]
  have heq : discNewtonPotential f = (fun z => (discNewtonReal (fun w => (f w).re) z : ℂ)) +
      Complex.I • (fun z => (discNewtonReal (fun w => (f w).im) z : ℂ)) :=
    funext (discNewtonPotential_eq_real_im hf.continuousOn)
  rw [heq]
  change (Δ ((Complex.ofRealCLM ∘ discNewtonReal (fun w => (f w).re)) +
      ((Complex.I • Complex.ofRealCLM) ∘ discNewtonReal (fun w => (f w).im)))) z = _
  rw [(Complex.ofRealCLM.contDiff.contDiffAt.comp z hrz).laplacian_add
    ((Complex.I • Complex.ofRealCLM).contDiff.contDiffAt.comp z hiz),
    hrz.laplacian_CLM_comp_left (l := Complex.ofRealCLM),
    hiz.laplacian_CLM_comp_left (l := Complex.I • Complex.ofRealCLM)]
  simp only [Function.comp_apply]
  have hRl : LeafCandidates.realPlanarLaplacian
      (discNewtonReal (fun w => (f w).re)) z = 2 * Real.pi * (f z).re :=
    discNewtonReal_laplacian (Complex.reCLM.contDiff.comp_contDiffOn hf) hz
  have hIl : LeafCandidates.realPlanarLaplacian
      (discNewtonReal (fun w => (f w).im)) z = 2 * Real.pi * (f z).im :=
    discNewtonReal_laplacian (Complex.imCLM.contDiff.comp_contDiffOn hf) hz
  rw [← L08_realPlanarLaplacian_eq_laplacian hrz,
    ← L08_realPlanarLaplacian_eq_laplacian hiz, hRl, hIl]
  apply Complex.ext <;> simp [Complex.real_smul, Complex.mul_re, Complex.mul_im]

end Yau.LeafProofs
