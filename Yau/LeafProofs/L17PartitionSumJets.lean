import Yau.LeafProofs.L17ScaledCutoffJets
import Yau.LeafProofs.L17PartitionSumBound
import Yau.LeafProofs.L17FinsumJets

/-! Uniform scaled jets of the genuine normalizing finsum. -/

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem UniformChartPartition.scaled_chartWeightSum_jet_le
    (P : UniformChartPartition g) (hρr : 2 * P.radius < P.charts.radius)
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hjet : ∀ (p : P.centers) q z, z ∈ ball (0 : ComplexVector n) 2 →
      ‖iteratedFDeriv ℝ k (fun w => chartWeight (P.charts.chart p) P.radius P.radius_pos
        (P.charts.chart q (P.radius • w))) z‖ ≤ C)
    (q : M.Carrier) {z : ComplexVector n} (hz : z ∈ ball 0 2) :
    ‖iteratedFDeriv ℝ k (fun w => chartWeightSum P.charts P.centers P.radius P.radius_pos
      (P.charts.chart q (P.radius • w))) z‖ ≤ (P.overlapBudget : ℝ) * C := by
  classical
  let x := P.charts.chart q (P.radius • z)
  obtain ⟨V, hV, hI, hcard⟩ := P.overlap x
  let I : Set P.centers :=
    {p | ((P.charts.chart p '' closedBall 0 P.radius) ∩ V).Nonempty}
  have hIF : I.Finite := by convert! hI using 1
  have hIcard : Nat.card I ≤ P.overlapBudget := by convert! hcard using 1
  let f (p : P.centers) (w : ComplexVector n) :=
    chartWeight (P.charts.chart p) P.radius P.radius_pos (P.charts.chart q (P.radius • w))
  have hfp (p : P.centers) : ContDiffAt ℝ k (f p) z :=
    ((smoothFn_comp_scaledChart_contDiffOn P.charts
      (P.charts.chartWeight_properties p P.radius_pos P.radius_lt).2.1
      P.radius_pos hρr q).contDiffAt (isOpen_ball.mem_nhds hz)).of_le (by simp)
  have hzNorm : ‖z‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hz
  have hzSource : P.radius • z ∈ (P.charts.chart q).source := by
    apply P.charts.closedBall_source q
    apply ball_subset_closedBall
    apply mem_ball.mpr
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos P.radius_pos]
    nlinarith [P.radius_pos]
  have hcont : ContinuousAt (fun w : ComplexVector n => P.charts.chart q (P.radius • w)) z :=
    ((P.charts.chart q).continuousOn.continuousAt
      ((P.charts.chart q).open_source.mem_nhds hzSource)).comp (by fun_prop)
  have hzero : ∀ᶠ w in 𝓝 z, ∀ p : P.centers, p ∉ hIF.toFinset → f p w = 0 := by
    filter_upwards [hcont.eventually hV] with w hw p hp
    by_contra hne
    have hts : P.charts.chart q (P.radius • w) ∈
        tsupport (chartWeight (P.charts.chart p) P.radius P.radius_pos) := subset_closure hne
    have himage := (P.charts.chartWeight_properties p P.radius_pos P.radius_lt).2.2 hts
    have himage' : P.charts.chart q (P.radius • w) ∈
        P.charts.chart p '' closedBall 0 P.radius := by
      apply image_mono _ himage
      intro u hu
      exact mem_closedBall.mpr ((mem_closedBall.mp hu).trans (by have := P.radius_pos; linarith))
    exact hp (hIF.mem_toFinset.mpr ⟨_, himage', hw⟩)
  have hsum := norm_iteratedFDeriv_finsum_le hIF.toFinset C (fun p _ => hfp p) hzero
    (fun p _ => hjet p q z hz)
  have hcardFin : hIF.toFinset.card ≤ P.overlapBudget := by
    rw [← Nat.card_eq_card_finite_toFinset hIF]
    exact hIcard
  exact hsum.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcardFin) hC)

theorem BoundedChartFamily.scaled_chartWeightSum_jet_bound
    (A : BoundedChartFamily g) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : UniformChartPartition g, P.charts = A →
      P.radius ≤ 1 → 2 * P.radius < A.radius → ∀ q z,
      z ∈ ball (0 : ComplexVector n) 2 →
      ‖iteratedFDeriv ℝ k (fun w => chartWeightSum P.charts P.centers P.radius P.radius_pos
        (P.charts.chart q (P.radius • w))) z‖ ≤ (P.overlapBudget : ℝ) * C := by
  obtain ⟨C, hC, hc⟩ := A.scaled_chartWeight_jet_bound k
  refine ⟨C, hC, ?_⟩
  intro P hA hρone hρr q z hz
  apply P.scaled_chartWeightSum_jet_le (by simpa only [hA] using hρr) k C hC.le _ q hz
  intro p q z hz
  simpa only [hA] using hc P.radius P.radius_pos hρone hρr p q z hz

end Yau.LeafProofs.L17Aux
