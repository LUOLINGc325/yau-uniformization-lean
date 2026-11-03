import Yau.LeafProofs.L17InteriorChartEscape

/-! Actual coordinate differences are controlled by short intrinsic distances. -/

noncomputable section

open Set Metric

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem BoundedChartFamily.chartBall_contains_distance_ball_from
    {g : HermitianField M} (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (p q : M.Carrier) (z₀ : ComplexVector n) {ρ : ℝ} (hρ : 0 < ρ)
    (hBG : closedBall z₀ ρ ⊆ ball 0 A.radius)
    (hq : inducedDistance g (A.chart p z₀) q < Real.sqrt (2 * (A.bound 0)⁻¹) * ρ) :
    q ∈ A.chart p '' ball z₀ ρ := by
  let c := Real.sqrt (2 * (A.bound 0)⁻¹)
  have hC := A.bound_pos 0
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 ≤ inducedDistance g (A.chart p z₀) q / c :=
    div_nonneg (L23Aux.inducedDistance_nonneg g hg _ _) hc.le
  have hlt : inducedDistance g (A.chart p z₀) q / c < ρ :=
    (div_lt_iff₀ hc).mpr (by simpa only [mul_comm] using hq)
  let σ := (ρ + inducedDistance g (A.chart p z₀) q / c) / 2
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσρ : σ < ρ := by dsimp [σ]; linarith
  have hbudget : inducedDistance g (A.chart p z₀) q < c * σ := by
    have hdiv : inducedDistance g (A.chart p z₀) q / c < σ := by dsimp [σ]; linarith
    exact ((div_lt_iff₀ hc).mp hdiv).trans_eq (mul_comm σ c)
  obtain ⟨z, hz, hqz⟩ := A.closedChartBall_contains_distance_ball_from hg p q z₀ hσ
    ((closedBall_subset_closedBall hσρ.le).trans hBG) hbudget
  exact ⟨z, (mem_closedBall.mp hz).trans_lt hσρ, hqz⟩

theorem BoundedChartFamily.coordinate_diff_le_distance
    {g : HermitianField M} (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (p q : M.Carrier) (z₀ : ComplexVector n) {ρ : ℝ} (hρ : 0 < ρ)
    (hBG : closedBall z₀ ρ ⊆ ball 0 A.radius)
    (hq : inducedDistance g (A.chart p z₀) q < Real.sqrt (2 * (A.bound 0)⁻¹) * ρ) :
    ‖(A.chart p).symm q - z₀‖ ≤
      (Real.sqrt (2 * (A.bound 0)⁻¹))⁻¹ * inducedDistance g (A.chart p z₀) q := by
  let c := Real.sqrt (2 * (A.bound 0)⁻¹)
  have hC := A.bound_pos 0
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 ≤ inducedDistance g (A.chart p z₀) q / c :=
    div_nonneg (L23Aux.inducedDistance_nonneg g hg _ _) hc.le
  have hqcoord : ‖(A.chart p).symm q - z₀‖ < ρ := by
    obtain ⟨z, hz, hqz⟩ := A.chartBall_contains_distance_ball_from hg p q z₀ hρ hBG hq
    have hs := A.closedBall_source p (ball_subset_closedBall (hBG (ball_subset_closedBall hz)))
    have hinv : (A.chart p).symm q = z := by rw [← hqz]; exact (A.chart p).left_inv hs
    rw [hinv]
    simpa only [mem_ball, dist_eq_norm] using hz
  suffices ‖(A.chart p).symm q - z₀‖ ≤ inducedDistance g (A.chart p z₀) q / c by
    simpa only [div_eq_inv_mul, c] using this
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  by_cases hbρ : b < ρ
  · have hbp : 0 < b := hd.trans_lt hb
    have hbudget : inducedDistance g (A.chart p z₀) q < c * b :=
      (div_lt_iff₀ hc).mp hb |>.trans_eq (mul_comm b c)
    obtain ⟨z, hz, hqz⟩ := A.closedChartBall_contains_distance_ball_from hg p q z₀ hbp
      ((closedBall_subset_closedBall hbρ.le).trans hBG) hbudget
    have hs := A.closedBall_source p (ball_subset_closedBall (hBG
      ((closedBall_subset_closedBall hbρ.le) hz)))
    have hinv : (A.chart p).symm q = z := by rw [← hqz]; exact (A.chart p).left_inv hs
    rw [hinv]
    simpa only [mem_closedBall, dist_eq_norm] using hz
  · exact hqcoord.le.trans (le_of_not_gt hbρ)

end Yau.LeafProofs.L17Aux
