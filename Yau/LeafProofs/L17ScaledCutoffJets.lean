import Yau.LeafProofs.L17ScaledExtensionJets

/-! Uniform scaled jets of the actual atlas weights and localization functions. -/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem BoundedChartFamily.scaled_chartLocalization_jet_bound
    (A : BoundedChartFamily g) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ ≤ 1 → 2 * ρ < A.radius →
      ∀ p q z, z ∈ ball (0 : ComplexVector n) 2 →
        ‖iteratedFDeriv ℝ k (fun w => chartLocalization (A.chart p) ρ hρ
          (A.chart q (ρ • w))) z‖ ≤ C := by
  let b := outerChartBump n 1 zero_lt_one
  have hbs : tsupport b ⊆ closedBall 0 1 := by
    rw [ContDiffBump.tsupport_eq]
    exact subset_rfl
  obtain ⟨C, hC, hc⟩ := A.scaledChartExtension_jet_bound b.contDiff b.hasCompactSupport hbs k
  refine ⟨C, hC, ?_⟩
  intro ρ hρ hρone hρr p q z hz
  have heq : (fun w => chartLocalization (A.chart p) ρ hρ (A.chart q (ρ • w))) =
      A.scaledChartExtension b ρ p q := by
    funext w
    exact congrArg (fun f : ComplexVector n → ℝ =>
      chartExtensionZero (A.chart p) f (A.chart q (ρ • w)))
        (funext (outerChartBump_rescale n hρ))
  rw [heq]
  exact hc ρ hρ hρone hρr p q z hz

theorem BoundedChartFamily.scaled_chartWeight_jet_bound
    (A : BoundedChartFamily g) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ ≤ 1 → 2 * ρ < A.radius →
      ∀ p q z, z ∈ ball (0 : ComplexVector n) 2 →
        ‖iteratedFDeriv ℝ k (fun w => chartWeight (A.chart p) ρ hρ
          (A.chart q (ρ • w))) z‖ ≤ C := by
  let b := innerChartBump n 1 zero_lt_one
  have hbs : tsupport b ⊆ closedBall 0 1 := by
    rw [ContDiffBump.tsupport_eq]
    exact closedBall_subset_closedBall (by dsimp [b, innerChartBump]; norm_num)
  obtain ⟨C, hC, hc⟩ := A.scaledChartExtension_jet_bound b.contDiff b.hasCompactSupport hbs k
  refine ⟨C, hC, ?_⟩
  intro ρ hρ hρone hρr p q z hz
  have heq : (fun w => chartWeight (A.chart p) ρ hρ (A.chart q (ρ • w))) =
      A.scaledChartExtension b ρ p q := by
    funext w
    exact congrArg (fun f : ComplexVector n → ℝ =>
      chartExtensionZero (A.chart p) f (A.chart q (ρ • w)))
        (funext (innerChartBump_rescale n hρ))
  rw [heq]
  exact hc ρ hρ hρone hρr p q z hz

end Yau.LeafProofs.L17Aux
