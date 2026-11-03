import Yau.LeafProofs.L10DiscEnergyDivergence

/-! Genuine within-disc jets and their actual interior derivatives. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace Yau.LeafProofs

def discEnergyPartial {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℂ → F) (v : ℂ) (z : ℂ) : F :=
  fderivWithin ℝ u (Metric.closedBall (0 : ℂ) 1) z v

theorem discEnergy_closedBall_mem_nhds {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
  mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall

theorem discEnergy_contDiffAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℂ → F} (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) : ContDiffAt ℝ ∞ u z :=
  hu.contDiffAt (discEnergy_closedBall_mem_nhds hz)

theorem discEnergyPartial_contDiffOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℂ → F} (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) (v : ℂ) :
    ContDiffOn ℝ ∞ (discEnergyPartial u v) (Metric.closedBall (0 : ℂ) 1) :=
  (hu.fderivWithin disc_closedBall_uniqueDiffOn (by simp)).clm_apply contDiffOn_const

theorem discEnergyPartial_eq_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℂ → F) (v : ℂ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discEnergyPartial u v z = fderiv ℝ u z v := by
  unfold discEnergyPartial
  rw [fderivWithin_of_mem_nhds (discEnergy_closedBall_mem_nhds hz)]

theorem discEnergyPartial_eq_fderiv_eventually {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℂ → F) (v : ℂ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discEnergyPartial u v =ᶠ[𝓝 z] (fun w => fderiv ℝ u w v) := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  exact discEnergyPartial_eq_fderiv u v hw

theorem discEnergyPartial_twice_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℂ → F) (v w : ℂ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discEnergyPartial (discEnergyPartial u v) w z =
      fderiv ℝ (fun y => fderiv ℝ u y v) z w := by
  rw [discEnergyPartial_eq_fderiv _ _ hz,
    (discEnergyPartial_eq_fderiv_eventually u v hz).fderiv_eq]

theorem discEnergyPartial_hasDerivAt_circle {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℂ → F} (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) (θ : ℝ) :
    HasDerivAt (fun t => u (L08_unitCircle t))
      (discEnergyPartial u (L08_unitCircle θ * Complex.I) (L08_unitCircle θ)) θ := by
  have hm (t : ℝ) : L08_unitCircle t ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right, L08_norm_unitCircle]
  exact ((hu.differentiableOn (by simp)) _ (hm θ)).hasFDerivWithinAt.comp_hasDerivAt θ
    (L08_hasDerivAt_unitCircle θ) (Eventually.of_forall hm)

/-- The smooth specialization keeps all boundary derivatives as within derivatives. -/
theorem discEnergy_integral_divergence_smooth {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F (Metric.closedBall (0 : ℂ) 1)) :
    (∫ z in Metric.ball (0 : ℂ) 1,
      (fderiv ℝ F z 1).re + (fderiv ℝ F z Complex.I).im) =
      ∫ θ in (-Real.pi)..Real.pi, inner ℝ (L08_unitCircle θ) (F (L08_unitCircle θ)) := by
  have hJ : ContDiffOn ℝ ∞ (fderivWithin ℝ F (Metric.closedBall (0 : ℂ) 1))
      (Metric.closedBall (0 : ℂ) 1) :=
    hF.fderivWithin disc_closedBall_uniqueDiffOn (by simp)
  have h := discEnergy_integral_divergence hF.continuousOn hJ.continuousOn
    (fun z hz => by
      rw [fderivWithin_of_mem_nhds (discEnergy_closedBall_mem_nhds hz)]
      exact (discEnergy_contDiffAt hF hz).differentiableAt (by simp) |>.hasFDerivAt)
  refine (setIntegral_congr_fun Metric.isOpen_ball.measurableSet (fun z hz => ?_)).trans h
  unfold discEnergyDivergence
  rw [fderivWithin_of_mem_nhds (discEnergy_closedBall_mem_nhds hz)]

end Yau.LeafProofs
