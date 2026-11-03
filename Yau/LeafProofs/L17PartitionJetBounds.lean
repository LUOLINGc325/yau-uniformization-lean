import Yau.LeafProofs.L17UniformPartitionJets

/-! The unit-scale partition budgets give the actual rho-to-the-minus-k chart bounds. -/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem unscale_backgroundChart_jet_bound
    (A : BoundedChartFamily g) {f : M.Carrier → ℝ} (hf : SmoothFn f)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : 2 * ρ < A.radius) (q : M.Carrier) (k : ℕ) (C : ℝ)
    (hb : ∀ z ∈ ball (0 : ComplexVector n) 2,
      ‖iteratedFDeriv ℝ k (fun w => f (A.chart q (ρ • w))) z‖ ≤ C)
    {z : ComplexVector n} (hz : z ∈ ball 0 (2 * ρ)) :
    ‖iteratedFDeriv ℝ k (fun w => f (A.chart q w)) z‖ ≤ C * (ρ⁻¹) ^ k := by
  have hzNorm : ‖z‖ < 2 * ρ := by simpa only [mem_ball, dist_zero_right] using hz
  have hscaled : ρ⁻¹ • z ∈ ball (0 : ComplexVector n) 2 := by
    apply mem_ball.mpr
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
    rw [← div_eq_inv_mul]
    exact (div_lt_iff₀ hρ).mpr hzNorm
  have h := norm_iteratedFDeriv_comp_smul_le isOpen_ball
    (smoothFn_comp_scaledChart_contDiffOn A hf hρ hρr q) ρ⁻¹ hscaled k
  have heq : (fun w : ComplexVector n => f (A.chart q (ρ • (ρ⁻¹ • w)))) =
      (fun w => f (A.chart q w)) := by
    funext w
    rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
  rw [heq, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hb _ hscaled) (by positivity))

theorem BoundedChartFamily.exists_uniform_partition_jet_budget
    (A : BoundedChartFamily g) (hg : MetricSmooth g) :
    ∃ N : ℕ, ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ ε : ℝ, 0 < ε →
      ∃ P : UniformChartPartition g, P.charts = A ∧ P.radius < ε ∧ P.radius ≤ 1 ∧
        2 * P.radius < A.radius ∧ P.overlapBudget = N ∧
        ∀ k (p : P.centers) q z, z ∈ ball (0 : ComplexVector n) (2 * P.radius) →
          ‖iteratedFDeriv ℝ k (fun w => P.weight p (P.charts.chart q w)) z‖ ≤
              C k * (P.radius⁻¹) ^ k ∧
          ‖iteratedFDeriv ℝ k (fun w => P.localization p (P.charts.chart q w)) z‖ ≤
              C k * (P.radius⁻¹) ^ k := by
  obtain ⟨N, C, hC, hP⟩ := A.exists_uniform_partition_scaled_jet_budget hg
  refine ⟨N, C, hC, ?_⟩
  intro ε hε
  obtain ⟨P, hA, hρε, hρone, hρr, hbudget, hbound⟩ := hP ε hε
  refine ⟨P, hA, hρε, hρone, hρr, hbudget, ?_⟩
  intro k p q z hz
  have hρrP : 2 * P.radius < P.charts.radius := by simpa only [hA] using hρr
  constructor
  · exact unscale_backgroundChart_jet_bound P.charts (P.weight_smooth p) P.radius_pos hρrP q k
      (C k) (fun w hw => (hbound k p q w hw).1) hz
  · exact unscale_backgroundChart_jet_bound P.charts (P.localization_smooth p) P.radius_pos hρrP q k
      (C k) (fun w hw => (hbound k p q w hw).2) hz

end Yau.LeafProofs.L17Aux
