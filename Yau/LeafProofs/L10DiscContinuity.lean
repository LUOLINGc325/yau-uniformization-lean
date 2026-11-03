import Yau.LeafProofs.L10DiscInterior
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! Removing a small disc around the moving pole produces uniformly
convergent continuous parameter integrals. -/

noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate Topology ContDiff

namespace Yau.LeafProofs

private def discKernelBump (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℂ) where
  rIn := r / 2
  rOut := r
  rIn_pos := half_pos hr
  rIn_lt_rOut := half_lt_self hr

private theorem discKernelBump_abs_le (r : ℝ) (hr : 0 < r) (v : ℂ) :
    |discKernelBump r hr v| ≤ 1 := by
  rw [abs_of_nonneg (discKernelBump r hr).nonneg]
  exact (discKernelBump r hr).le_one

/-- A uniform `O(r)` bound for the integral of the norm near a moving
pole gives continuity up to any closed parameter set. -/
theorem disc_integral_continuousOn_of_near_mass
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : ℂ → ℂ → E} {S : Set ℂ} {A B : ℝ} (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hInt : ∀ z ∈ S, IntegrableOn (K z) (Metric.ball (0 : ℂ) 1) volume)
    (hCont : ∀ z ∈ S, ∀ w ∈ Metric.ball (0 : ℂ) 1, z ≠ w →
      ContinuousWithinAt (fun y => K y w) S z)
    (hBound : ∀ z ∈ S, ∀ w ∈ Metric.ball (0 : ℂ) 1, z ≠ w →
      ‖K z w‖ ≤ B * ‖z - w‖⁻¹)
    (hNear : ∀ z ∈ S, ∀ r : ℝ, 0 < r →
      (∫ w in Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r, ‖K z w‖) ≤ A * r) :
    ContinuousOn (fun z => ∫ w in Metric.ball (0 : ℂ) 1, K z w) S := by
  let T : (r : ℝ) → 0 < r → ℂ → E := fun r hr z =>
    ∫ w in Metric.ball (0 : ℂ) 1, (1 - discKernelBump r hr (z - w)) • K z w
  have hTInt : ∀ r hr z, z ∈ S → IntegrableOn
      (fun w => (1 - discKernelBump r hr (z - w)) • K z w)
      (Metric.ball (0 : ℂ) 1) volume := by
    intro r hr z hz
    apply (hInt z hz).bdd_smul 1
    · exact (continuous_const.sub ((discKernelBump r hr).continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · filter_upwards with w
      rw [Real.norm_of_nonneg (sub_nonneg.mpr (discKernelBump r hr).le_one)]
      linarith [(discKernelBump r hr).nonneg (x := z - w)]
  have hTCont : ∀ r hr, ContinuousOn (T r hr) S := by
    intro r hr
    apply continuousOn_of_dominated
      (bound := fun _ : ℂ => B * (r / 2)⁻¹)
    · intro z hz
      exact (hTInt r hr z hz).aestronglyMeasurable
    · intro z hz
      filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
      by_cases hd : ‖z - w‖ ≤ r / 2
      · have hφ : discKernelBump r hr (z - w) = 1 :=
          (discKernelBump r hr).one_of_mem_closedBall (by simpa [discKernelBump] using hd)
        simp only [hφ, sub_self, zero_smul, norm_zero]
        positivity
      · have hdpos : 0 < ‖z - w‖ := (half_pos hr).trans (lt_of_not_ge hd)
        have hc : ‖1 - discKernelBump r hr (z - w)‖ ≤ 1 := by
          rw [Real.norm_of_nonneg (sub_nonneg.mpr (discKernelBump r hr).le_one)]
          linarith [(discKernelBump r hr).nonneg (x := z - w)]
        rw [norm_smul]
        calc
          _ ≤ 1 * (B * ‖z - w‖⁻¹) := mul_le_mul hc
            (hBound z hz w hw (sub_ne_zero.mp (norm_pos_iff.mp hdpos))) (norm_nonneg _) (by norm_num)
          _ ≤ B * (r / 2)⁻¹ := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_left
              ((inv_le_inv₀ hdpos (half_pos hr)).2 (le_of_not_ge hd)) hB
    · exact integrableOn_const (Metric.isBounded_ball.measure_lt_top.ne)
    · filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
      intro z hz
      by_cases hzw : z = w
      · have hzero : (fun y : ℂ => 1 - discKernelBump r hr (y - w)) =ᶠ[𝓝 z] 0 := by
          have ht : Tendsto (fun y : ℂ => y - w) (𝓝 z) (𝓝 (0 : ℂ)) := by
            simpa [hzw, Pi.sub_def, id_eq] using ((continuous_id.sub continuous_const : Continuous (fun y : ℂ => y - w)).continuousAt (x := z)).tendsto
          filter_upwards [ht.eventually (discKernelBump r hr).eventuallyEq_one] with y hy
          simp [hy]
        apply (continuousWithinAt_const (b := (0 : E))).congr_of_eventuallyEq_of_mem _ hz
        filter_upwards [hzero.filter_mono nhdsWithin_le_nhds] with y hy
        simp [hy]
      · exact (continuous_const.sub ((discKernelBump r hr).continuous.comp (continuous_id.sub continuous_const))).continuousWithinAt.smul (hCont z hz w hw hzw)
  have hApprox : ∀ r hr z, z ∈ S →
      ‖(∫ w in Metric.ball (0 : ℂ) 1, K z w) - T r hr z‖ ≤ A * r := by
    intro r hr z hz
    have hφInt : IntegrableOn (fun w => discKernelBump r hr (z - w) • K z w)
        (Metric.ball (0 : ℂ) 1) volume := by
      apply (hInt z hz).bdd_smul 1
      · exact ((discKernelBump r hr).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      · exact Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using discKernelBump_abs_le r hr (z - w)
    have hEq : (∫ w in Metric.ball (0 : ℂ) 1, K z w) - T r hr z =
        ∫ w in Metric.ball (0 : ℂ) 1, discKernelBump r hr (z - w) • K z w := by
      dsimp only [T]
      rw [← integral_sub (hInt z hz) (hTInt r hr z hz)]
      apply integral_congr_ae
      filter_upwards with w
      simp [sub_smul]
    rw [hEq, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball
      (Set.inter_subset_left : Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r ⊆ Metric.ball 0 1)]
    · calc
        _ ≤ ∫ w in Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r,
            ‖discKernelBump r hr (z - w) • K z w‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ w in Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r, ‖K z w‖ := by
          apply integral_mono_ae
            (hφInt.mono_set Set.inter_subset_left).norm ((hInt z hz).mono_set Set.inter_subset_left).norm
          exact Eventually.of_forall fun w => by
            dsimp only
            rw [norm_smul, Real.norm_eq_abs]
            simpa using mul_le_mul_of_nonneg_right (discKernelBump_abs_le r hr (z - w)) (norm_nonneg (K z w))
        _ ≤ A * r := hNear z hz r hr
    · intro w hw
      have hd : r ≤ ‖z - w‖ := by
        have hn : w ∉ Metric.ball z r := fun h => hw.2 ⟨hw.1, h⟩
        simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hn
      rw [(discKernelBump r hr).zero_of_le_dist (by simpa [discKernelBump] using hd), zero_smul]
  obtain ⟨r, _, hr, hrlim⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  have hlim : TendstoUniformlyOn (fun n => T (r n) (hr n))
      (fun z => ∫ w in Metric.ball (0 : ℂ) 1, K z w) atTop S := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have he : ∀ᶠ n in atTop, A * r n < ε :=
      (tendsto_const_nhds.mul hrlim).eventually (gt_mem_nhds (by simpa using hε))
    filter_upwards [he] with n hn
    intro z hz
    exact (show dist (∫ w in Metric.ball (0 : ℂ) 1, K z w) (T (r n) (hr n) z) ≤ A * r n by
      simpa [dist_eq_norm] using hApprox (r n) (hr n) z hz).trans_lt hn
  exact hlim.continuousOn (Eventually.of_forall fun n => hTCont (r n) (hr n)).frequently

end Yau.LeafProofs
