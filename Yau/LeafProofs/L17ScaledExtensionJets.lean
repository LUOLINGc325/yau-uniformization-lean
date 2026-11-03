import Yau.LeafProofs.L17ScaledTransitionJets

/-! Uniform unit-scale jets for actual zero-extended coordinate cutoffs. -/

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def BoundedChartFamily.scaledChartExtension (A : BoundedChartFamily g)
    (b : ComplexVector n → ℝ) (ρ : ℝ) (p q : M.Carrier) (z : ComplexVector n) : ℝ :=
  chartExtensionZero (A.chart p) (fun w => b (ρ⁻¹ • w)) (A.chart q (ρ • z))

set_option maxHeartbeats 1600000 in
theorem BoundedChartFamily.scaledChartExtension_jet_bound
    (A : BoundedChartFamily g) {b : ComplexVector n → ℝ}
    (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hbs : tsupport b ⊆ closedBall 0 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → 2 * ρ < A.radius →
      ∀ p q z, z ∈ ball (0 : ComplexVector n) 2 →
        ‖iteratedFDeriv ℝ k (A.scaledChartExtension b ρ p q) z‖ ≤ C := by
  classical
  obtain ⟨D, hD, hd⟩ := hbc.exists_bound_iteratedFDeriv hb k
  have hbjets : UniformJetBounds k (fun _ : ChartScaleIndex M => b) (fun _ => univ) :=
    ⟨max 1 D, le_max_left _ _, fun _ z _ j hj => (hd j hj z).trans (le_max_right _ _)⟩
  have hcomp := (A.scaledTransition_uniformJetBounds k).comp hbjets
    A.scaledTransitionDomain_isOpen (fun _ => isOpen_univ) A.scaledTransition_smooth
    (fun _ => hb.contDiffOn) (fun _ _ _ => mem_univ _)
  obtain ⟨C, hC, hc⟩ := hcomp
  refine ⟨C, zero_lt_one.trans_le hC, ?_⟩
  intro ρ hρ hρone hρr p q z hz
  let φ : ComplexVector n → ℝ := fun w => b (ρ⁻¹ • w)
  let χ : M.Carrier → ℝ := chartExtensionZero (A.chart p) φ
  let a : ChartScaleIndex M := (⟨ρ, hρ, hρone⟩, (q, p))
  have hρr' : ρ < A.radius := by linarith
  have hφ : ContDiff ℝ ∞ φ := by
    have hL : ContDiff ℝ ∞ (fun w : ComplexVector n => ρ⁻¹ • w) := by
      convert! (ρ⁻¹ • ContinuousLinearMap.id ℝ (ComplexVector n)).contDiff using 1
    exact hb.comp hL
  have hφs : tsupport φ ⊆ closedBall 0 ρ := by
    apply closure_minimal _ isClosed_closedBall
    intro w hw
    have harg : ρ⁻¹ • w ∈ tsupport b := subset_closure hw
    have hn : ρ⁻¹ * ‖w‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hρ)] using hbs harg
    apply mem_closedBall.mpr
    rw [dist_zero_right]
    exact (div_le_one hρ).mp (by simpa only [div_eq_inv_mul] using hn)
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall (0 : ComplexVector n) ρ).of_isClosed_subset (isClosed_tsupport φ) hφs
  have hφsource : tsupport φ ⊆ (A.chart p).source := by
    intro w hw
    apply A.closedBall_source p
    exact mem_closedBall.mpr ((mem_closedBall.mp (hφs hw)).trans hρr'.le)
  obtain ⟨_, _, hχs⟩ := chartExtensionZero_properties (A.chart p)
    (A.inverse_differentiable p) hφ hφc hφsource
  have hχimage : tsupport χ ⊆ A.chart p '' closedBall 0 ρ :=
    hχs.trans (image_mono hφs)
  have hzNorm : ‖z‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hz
  have hzNative : ρ • z ∈ ball 0 A.radius := by
    apply mem_ball.mpr
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    nlinarith
  have hzSource := A.closedBall_source q (ball_subset_closedBall hzNative)
  by_cases hx : A.chart q (ρ • z) ∈ tsupport χ
  · obtain ⟨w, hw, hweq⟩ := hχimage hx
    have hws : w ∈ (A.chart p).source := A.closedBall_source p
      (mem_closedBall.mpr ((mem_closedBall.mp hw).trans hρr'.le))
    have htarget : A.chart q (ρ • z) ∈ (A.chart p).target := by
      rw [← hweq]
      exact (A.chart p).map_source hws
    have hcoord : A.transitionMap (q, p) (ρ • z) = w := by
      change (A.chart p).symm (A.chart q (ρ • z)) = w
      rw [← hweq, (A.chart p).left_inv hws]
    have htargetcoord : A.transitionMap (q, p) (ρ • z) ∈ ball 0 A.radius := by
      rw [hcoord]
      exact (mem_closedBall.mp hw).trans_lt hρr'
    have hnative : ρ • z ∈ A.transitionBallDomain (q, p) :=
      ⟨hzNative, ⟨hzSource, htarget⟩, htargetcoord⟩
    have hscaled : ‖A.scaledTransitionMap a z‖ ≤ 1 := by
      change ‖ρ⁻¹ • A.transitionMap (q, p) (ρ • z)‖ ≤ 1
      rw [hcoord, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
      rw [← div_eq_inv_mul]
      apply (div_le_one hρ).mpr
      simpa only [mem_closedBall, dist_zero_right] using hw
    have hdomT : A.scaledTransitionMap a z ∈ ball 0 2 :=
      mem_ball.mpr (by rw [dist_zero_right]; linarith)
    have hdom : z ∈ A.scaledTransitionDomain a := ⟨hnative, hdomT⟩
    have heq : A.scaledChartExtension b ρ p q =ᶠ[𝓝 z]
        (fun v => b (A.scaledTransitionMap a v)) := by
      filter_upwards [(A.scaledTransitionDomain_isOpen a).mem_nhds hdom] with v hv
      have ht : A.chart q (ρ • v) ∈ (A.chart p).target := hv.1.2.1.2
      change chartExtensionZero (A.chart p) φ (A.chart q (ρ • v)) = _
      simp only [chartExtensionZero, ite_eq_left ht]
      rfl
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
    exact hc a z hdom k le_rfl
  · have hcont : ContinuousAt (fun v : ComplexVector n => A.chart q (ρ • v)) z :=
      ((A.chart q).continuousOn.continuousAt
        ((A.chart q).open_source.mem_nhds hzSource)).comp (by fun_prop)
    have hO : (tsupport χ)ᶜ ∈ 𝓝 (A.chart q (ρ • z)) :=
      (isClosed_tsupport χ).isOpen_compl.mem_nhds hx
    have heq : A.scaledChartExtension b ρ p q =ᶠ[𝓝 z] (0 : ComplexVector n → ℝ) := by
      filter_upwards [hcont.eventually hO] with v hv
      change χ (A.chart q (ρ • v)) = 0
      by_contra hne
      exact hv (subset_closure hne)
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds, ← iteratedFDerivWithin_univ,
      iteratedFDerivWithin_zero]
    simpa only [Pi.zero_apply, norm_zero] using zero_le_one.trans hC

end Yau.LeafProofs.L17Aux
