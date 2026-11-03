import Yau.LeafProofs.L17SourceLocalizationTime
import Yau.LeafProofs.L17HolderProduct
import Yau.LeafProofs.L17HolderChartBounds
import Yau.LeafProofs.L17PartitionHolderBudget

/-! The original computed partition weight localizes the original forcing.
Its actual coordinate support collar makes the total zero extension continuous. -/

open Set Metric Filter
open scoped Topology
noncomputable section
namespace Yau.LeafProofs.L17SourceLocalizationAux
open L17Aux L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def localizedSource (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (q : ComplexVector n × ℝ) : ℝ := by
  classical
  exact if q.1 ∈ ball (0 : ComplexVector n) P.radius then
    P.weight p (P.charts.chart p q.1) * holderFun f (P.charts.chart p q.1, timeClamp T hT q.2)
    else 0

theorem localizedSource_formula (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) {z : ComplexVector n} {τ : ℝ}
    (hz : z ∈ ball (0 : ComplexVector n) P.radius) (hτ : τ ∈ Icc (0 : ℝ) T) :
    localizedSource P T hT f p (z, τ) = P.weight p (P.charts.chart p z) * holderFun f (P.charts.chart p z, ⟨τ,hτ⟩) := by
  simp only [localizedSource, hz, ite_true]
  congr 2
  exact Prod.ext rfl (projIcc_of_mem hT hτ)

theorem weight_coordinate_mem_closedBall (P : UniformChartPartition g) (p : P.centers)
    {z : ComplexVector n} (hz : z ∈ ball (0 : ComplexVector n) P.radius)
    (hnz : P.weight p (P.charts.chart p z) ≠ 0) : z ∈ closedBall (0 : ComplexVector n) (P.radius / 2) := by
  have hs : tsupport (P.weight p) ⊆ P.charts.chart p '' closedBall (0 : ComplexVector n) (P.radius / 2) :=
    (normalizedChartWeight_tsupport_subset P.charts P.centers P.radius_pos p).trans
      (P.charts.chartWeight_properties p P.radius_pos P.radius_lt).2.2
  obtain ⟨w, hw, he⟩ := hs (subset_tsupport _ hnz)
  have hzs : z ∈ (P.charts.chart p).source := P.charts.closedBall_source p
    (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) hz))
  have hws : w ∈ (P.charts.chart p).source := P.charts.closedBall_source p
    ((closedBall_subset_closedBall (by linarith [P.radius_lt, P.radius_pos])) hw)
  have h := congrArg (P.charts.chart p).symm he
  rw [(P.charts.chart p).left_inv hws, (P.charts.chart p).left_inv hzs] at h
  exact h ▸ hw

theorem localizedSource_eq_zero_outside_half (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (z : ComplexVector n) (τ : ℝ)
    (hz : z ∉ closedBall (0 : ComplexVector n) (P.radius / 2)) :
    localizedSource P T hT f p (z,τ) = 0 := by
  by_cases hzb : z ∈ ball (0 : ComplexVector n) P.radius
  · have hw : P.weight p (P.charts.chart p z) = 0 := by
      by_contra hn
      exact hz (weight_coordinate_mem_closedBall P p hzb hn)
    simp only [localizedSource, hzb, ite_true, hw, zero_mul]
  · simp only [localizedSource, hzb, ite_false]

theorem localizedSource_tsupport_slice (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (τ : ℝ) :
    tsupport (fun z => localizedSource P T hT f p (z,τ)) ⊆ closedBall (0 : ComplexVector n) (P.radius / 2) := by
  apply closure_minimal ?_ isClosed_closedBall
  intro z hz
  by_contra hn
  exact hz (localizedSource_eq_zero_outside_half P T hT f p z τ hn)

theorem localizedSource_continuous (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) : Continuous (localizedSource P T hT f p) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hz : q.1 ∈ ball (0 : ComplexVector n) P.radius
  · have hsource : q.1 ∈ (P.charts.chart p).source := P.charts.closedBall_source p
      (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) hz))
    have he : ContinuousAt (fun r : ComplexVector n × ℝ => P.charts.chart p r.1) q :=
      ((P.charts.chart p).continuousOn.continuousAt ((P.charts.chart p).open_source.mem_nhds hsource)).comp continuousAt_fst
    have ht : ContinuousAt (fun r : ComplexVector n × ℝ => timeClamp T hT r.2) q :=
      (timeClamp_continuous T hT).continuousAt.comp continuousAt_snd
    have hf := f.val.1.continuous.continuousAt.comp (he.prodMk ht)
    have hw := (L18Aux.contMDiff_real_of_smoothFn (P.weight_smooth p)).continuous.continuousAt.comp he
    have hEq : localizedSource P T hT f p =ᶠ[𝓝 q]
        (fun r => P.weight p (P.charts.chart p r.1) * holderFun f (P.charts.chart p r.1,timeClamp T hT r.2)) := by
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hz)] with r hr
      change r.1 ∈ ball (0 : ComplexVector n) P.radius at hr
      simp only [localizedSource, hr, ite_true]
    exact (hw.mul hf).congr_of_eventuallyEq hEq
  · have hhalf : q.1 ∉ closedBall (0 : ComplexVector n) (P.radius / 2) := fun hh =>
      hz ((closedBall_subset_ball (by linarith [P.radius_pos])) hh)
    have hEq : localizedSource P T hT f p =ᶠ[𝓝 q] (fun _ => 0) := by
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (isClosed_closedBall.isOpen_compl.mem_nhds hhalf)] with r hr
      exact localizedSource_eq_zero_outside_half P T hT f p r.1 r.2 hr
    exact continuousAt_const.congr_of_eventuallyEq hEq

theorem localizedSource_add (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f h : HolderSpace P T γ) (p : P.centers) :
    localizedSource P T hT (f + h) p = localizedSource P T hT f p + localizedSource P T hT h p := by
  funext q
  by_cases hz : q.1 ∈ ball (0 : ComplexVector n) P.radius
  · simp only [localizedSource, hz, ite_true, Pi.add_apply]
    change _ * (holderFun f _ + holderFun h _) = _ * holderFun f _ + _ * holderFun h _
    ring
  · simp only [localizedSource, hz, ite_false, Pi.add_apply, add_zero]

theorem localizedSource_smul (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (c : ℝ) (f : HolderSpace P T γ) (p : P.centers) :
    localizedSource P T hT (c • f) p = c • localizedSource P T hT f p := by
  funext q
  by_cases hz : q.1 ∈ ball (0 : ComplexVector n) P.radius
  · simp only [localizedSource, hz, ite_true, Pi.smul_apply, smul_eq_mul]
    change _ * (c * holderFun f _) = c * (_ * holderFun f _)
    ring
  · simp only [localizedSource, hz, ite_false, Pi.smul_apply, smul_eq_mul, mul_zero]

end Yau.LeafProofs.L17SourceLocalizationAux
