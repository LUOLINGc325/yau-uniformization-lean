import Yau.Proofs.D02RieszBall

open MeasureTheory Filter Set
open scoped Topology ContDiff CompactlySupported

noncomputable section
namespace Yau.NodeProofs.D02RieszAux

/-- A point mass strictly below a threshold admits an interior disc with mass
below the same threshold and a zero-mass boundary sphere. Only local finiteness
inside the domain is used. -/
theorem exists_small_mass_continuity_ball {U : Set ℂ} (hU : IsOpen U)
    {μ : Measure ℂ} (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ U → μ K < ⊤)
    {z : ℂ} (hz : z ∈ U) {b : ENNReal} (hatom : μ {z} < b) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall z r ⊆ U ∧
      μ (Metric.ball z r) < b ∧ μ (Metric.sphere z r) = 0 := by
  obtain ⟨R, hR, hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  let K := Metric.closedBall z R
  let σ := μ.restrict K
  letI : IsFiniteMeasure σ := ⟨by
    simpa only [σ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      hμ K (isCompact_closedBall z R) hRU⟩
  have hσatom : σ {z} < b := by
    dsimp only [σ]
    rw [Measure.restrict_apply (measurableSet_singleton z),
      inter_eq_left.mpr (singleton_subset_iff.mpr (Metric.mem_closedBall_self hR.le))]
    exact hatom
  obtain ⟨O, hzO, hOo, hσO⟩ := ({z} : Set ℂ).exists_isOpen_lt_of_lt b hσatom
  obtain ⟨a, ha, haO⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hOo.inter Metric.isOpen_ball).mem_nhds
      (show z ∈ O ∩ Metric.ball z R from ⟨hzO (mem_singleton z), Metric.mem_ball_self hR⟩))
  obtain ⟨r, hr, hzero⟩ := exists_null_frontier_thickening σ ({z} : Set ℂ) (a := 0) (b := a) ha
  have hr0 : 0 < r := hr.1
  have hsub : Metric.closedBall z r ⊆ O ∩ Metric.ball z R :=
    (Metric.closedBall_subset_closedBall hr.2.le).trans haO
  have hKsub : Metric.closedBall z r ⊆ K :=
    fun w hw ↦ Metric.ball_subset_closedBall (hsub hw).2
  have hσsphere : σ (Metric.sphere z r) = 0 := by
    simpa only [Metric.thickening_singleton, frontier_ball z hr0.ne'] using hzero
  have hballEq : σ (Metric.ball z r) = μ (Metric.ball z r) := by
    dsimp only [σ]
    rw [Measure.restrict_apply measurableSet_ball,
      inter_eq_left.mpr (Metric.ball_subset_closedBall.trans hKsub)]
  have hsphereEq : σ (Metric.sphere z r) = μ (Metric.sphere z r) := by
    dsimp only [σ]
    rw [Measure.restrict_apply Metric.isClosed_sphere.measurableSet,
      inter_eq_left.mpr (Metric.sphere_subset_closedBall.trans hKsub)]
  refine ⟨r, hr0, hKsub.trans hRU, ?_, ?_⟩
  · rw [← hballEq]
    exact (measure_mono (fun w hw ↦ (hsub (Metric.ball_subset_closedBall hw)).1)).trans_lt hσO
  · rw [← hsphereEq]
    exact hσsphere

/-- The continuity disc can be chosen before passing to the smooth sequence;
its strict mass bound then holds for every sufficiently late smooth Riesz measure. -/
theorem exists_disc_eventually_mass_lt {U : Set ℂ} (hU : IsOpen U)
    {v : ℕ → ℂ → ℝ} {μ : Measure ℂ}
    (hv : ∀ j, ContDiffOn ℝ ∞ (v j) U)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ U → μ K < ⊤)
    (hvague : ∀ f : C_c(ℂ, ℝ), tsupport f ⊆ U →
      Tendsto (fun j ↦ ∫ z, f z ∂smoothRieszOn U (v j)) atTop (𝓝 (∫ z, f z ∂μ)))
    {z : ℂ} (hz : z ∈ U) {b : ENNReal} (hatom : μ {z} < b) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall z r ⊆ U ∧
      μ (Metric.ball z r) < b ∧ μ (Metric.sphere z r) = 0 ∧
      ∀ᶠ j in atTop, LeafCandidates.smoothRieszMeasure (v j) z r univ < b := by
  obtain ⟨r, hr, hball, hmass, hzero⟩ := exists_small_mass_continuity_ball hU hμ hz hatom
  exact ⟨r, hr, hball, hmass, hzero, L08_eventually_mass_lt hU hv hμ hvague z r hball hzero hmass⟩

end Yau.NodeProofs.D02RieszAux
