import Yau.LeafProofs.L17LocalizedSchauderRawSum
import Yau.LeafProofs.L17SchauderSpaceLocal
import Yau.LeafProofs.L17HolderEmbedding

open Set Metric Filter
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17LocalScalarAssemblyAux
open L17Aux L17HolderAux L17SchauderAux L17LocalizedSchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def weightedLocalFunction (P : UniformChartPartition g) {T γ : ℝ}
    (u : LocalHolderSpace ℝ P T γ) (p : P.centers) (q : ComplexVector n × Time T) : ℝ :=
  if hz : q.1 ∈ ball (0 : ComplexVector n) P.radius then
    P.weight p (P.charts.chart p q.1)*localFun ℝ u ⟨p,(⟨q.1,hz⟩,q.2)⟩ else 0

def scalarAssemblyTerm (P : UniformChartPartition g) {T γ : ℝ}
    (u : LocalHolderSpace ℝ P T γ) (p : P.centers) (q : Cylinder M T) : ℝ :=
  if hx : q.1 ∈ (P.charts.chart p).target then
    if hz : (P.charts.chart p).symm q.1 ∈ ball (0 : ComplexVector n) P.radius then
      P.weight p q.1*localFun ℝ u ⟨p,(⟨(P.charts.chart p).symm q.1,hz⟩,q.2)⟩ else 0
  else 0

def scalarAssemblyFunction (P : UniformChartPartition g) {T γ : ℝ}
    (u : LocalHolderSpace ℝ P T γ) (q : Cylinder M T) : ℝ :=
  ∑ᶠ p : P.centers, scalarAssemblyTerm P u p q

theorem weight_nonzero_mem_half_cover (P : UniformChartPartition g) (p : P.centers)
    {x : M.Carrier} (hx : P.weight p x ≠ 0) :
    x ∈ P.charts.chart p '' closedBall (0 : ComplexVector n) (P.radius/2) := by
  have hs : tsupport (P.weight p) ⊆ P.charts.chart p '' closedBall (0 : ComplexVector n) (P.radius/2) :=
    (normalizedChartWeight_tsupport_subset P.charts P.centers P.radius_pos p).trans
      (P.charts.chartWeight_properties p P.radius_pos P.radius_lt).2.2
  exact hs (subset_tsupport _ hx)

theorem weight_nonzero_target_inverse_ball (P : UniformChartPartition g) (p : P.centers)
    {x : M.Carrier} (hx : P.weight p x ≠ 0) :
    x ∈ (P.charts.chart p).target ∧ (P.charts.chart p).symm x ∈ ball (0 : ComplexVector n) P.radius := by
  obtain ⟨w,hw,rfl⟩ := weight_nonzero_mem_half_cover P p hx
  have hs : w ∈ (P.charts.chart p).source := P.charts.closedBall_source p
    ((closedBall_subset_closedBall (by linarith [P.radius_lt,P.radius_pos])) hw)
  refine ⟨(P.charts.chart p).map_source hs,?_⟩
  rw [(P.charts.chart p).left_inv hs]
  exact (closedBall_subset_ball (by linarith [P.radius_pos])) hw

theorem weight_coordinate_mem_half (P : UniformChartPartition g) (p : P.centers)
    {z : ComplexVector n} (hz : z ∈ ball (0 : ComplexVector n) P.radius)
    (hw : P.weight p (P.charts.chart p z) ≠ 0) :
    z ∈ closedBall (0 : ComplexVector n) (P.radius/2) := by
  obtain ⟨w,hh,he⟩ := weight_nonzero_mem_half_cover P p hw
  have hzs : z ∈ (P.charts.chart p).source := P.charts.closedBall_source p
    (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) hz))
  have hws : w ∈ (P.charts.chart p).source := P.charts.closedBall_source p
    ((closedBall_subset_closedBall (by linarith [P.radius_lt,P.radius_pos])) hh)
  have h := congrArg (P.charts.chart p).symm he
  rw [(P.charts.chart p).left_inv hws,(P.charts.chart p).left_inv hzs] at h
  exact h ▸ hh

theorem weightedLocalFunction_zero_outside_half (P : UniformChartPartition g) {T γ : ℝ}
    (u : LocalHolderSpace ℝ P T γ) (p : P.centers) {z : ComplexVector n}
    (hz : z ∉ closedBall (0 : ComplexVector n) (P.radius/2)) (t : Time T) :
    weightedLocalFunction P u p (z,t)=0 := by
  by_cases hzb : z ∈ ball (0 : ComplexVector n) P.radius
  · have hw : P.weight p (P.charts.chart p z)=0 := by
      by_contra hn
      exact hz (weight_coordinate_mem_half P p hzb hn)
    simp only [weightedLocalFunction,dif_pos hzb,hw,zero_mul]
  · simp only [weightedLocalFunction,dif_neg hzb]

theorem weightedLocalFunction_zero_outside (P : UniformChartPartition g) {T γ : ℝ}
    (u : LocalHolderSpace ℝ P T γ) (p : P.centers) (z : ComplexVector n)
    (hz : z ∉ closedBall (0 : ComplexVector n) P.radius) (t : Time T) :
    weightedLocalFunction P u p (z,t)=0 :=
  weightedLocalFunction_zero_outside_half P u p
    (fun hh => hz ((closedBall_subset_closedBall (by linarith [P.radius_pos])) hh)) t

theorem weightedLocalFunction_abs_le (P : UniformChartPartition g) {T γ : ℝ}
    (u : LocalHolderSpace ℝ P T γ) (p : P.centers) (q : ComplexVector n × Time T) :
    |weightedLocalFunction P u p q| ≤ ‖u‖ := by
  by_cases hz : q.1 ∈ ball (0 : ComplexVector n) P.radius
  · rw [weightedLocalFunction,dif_pos hz,abs_mul,
      abs_of_nonneg (P.weight_nonneg p _)]
    have h := localValue_norm_le ℝ u ⟨p,(⟨q.1,hz⟩,q.2)⟩
    exact (mul_le_mul (P.weight_le_one p _) (by simpa only [Real.norm_eq_abs] using h)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  · simp only [weightedLocalFunction,dif_neg hz,abs_zero]
    exact norm_nonneg u

theorem weightedLocalFunction_nonzero_mem_half (P : UniformChartPartition g) {T γ : ℝ}
    (u : LocalHolderSpace ℝ P T γ) (p : P.centers) {q : ComplexVector n × Time T}
    (hq : weightedLocalFunction P u p q ≠ 0) :
    q.1 ∈ closedBall (0 : ComplexVector n) (P.radius/2) := by
  by_contra hn
  exact hq (weightedLocalFunction_zero_outside_half P u p hn q.2)

theorem rawLocalizedTerm_weighted_eq (P : UniformChartPartition g) {T γ : ℝ}
    (u : LocalHolderSpace ℝ P T γ) (p : P.centers) (q : Cylinder M T) :
    rawLocalizedTerm P T p (weightedLocalFunction P u p) q=scalarAssemblyTerm P u p q := by
  by_cases hx : q.1 ∈ (P.charts.chart p).target
  · rw [rawLocalizedTerm_eq_of_target P T p _ (weightedLocalFunction_zero_outside P u p) q hx]
    simp only [weightedLocalFunction,scalarAssemblyTerm,dif_pos hx,(P.charts.chart p).right_inv hx]
  · have hn : q.1 ∉ P.charts.chart p '' closedBall 0 P.radius := by
      rintro ⟨z,hz,he⟩
      apply hx
      rw [← he]
      exact (P.charts.chart p).map_source (P.charts.closedBall_source p
        ((closedBall_subset_closedBall P.radius_lt.le) hz))
    simp only [rawLocalizedTerm,if_neg hn,scalarAssemblyTerm,dif_neg hx]

end Yau.LeafProofs.L17LocalScalarAssemblyAux
