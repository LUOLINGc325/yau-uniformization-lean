import Yau.Proofs.F01NormalizedAtlasSmoothRecovery

/-! The normalized terminal clock recovers exactly the original open
time interval on both sides of the terminal face. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothSpaceTime_on_actual_terminal_interval_of_normalized_profiles
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (U : M.Carrier → ℝ → ℝ) {σ : ℝ} (hσ : 0 < σ) (hσr : σ ≤ A.radius)
    (T r : ℝ)
    (hProfiles : ∀ a, ContDiffOn ℝ ∞ (shiftedNativePotential A U a σ T)
      (ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) r)) :
    SmoothSpaceTime U (Ioo (T - σ ^ 2 / 4) (T + σ ^ 2 * r)) := by
  have hh := smoothSpaceTime_of_normalized_terminal_profiles g hg A U hσ hσr T
    (Ioo (-(1 / 4 : ℝ)) r) hProfiles
  intro a
  apply (hh a).mono
  intro p hp
  refine ⟨hp.1, ?_, ?_⟩
  · apply (lt_div_iff₀ (sq_pos_of_pos hσ)).mpr
    linarith [hp.2.1]
  · apply (div_lt_iff₀ (sq_pos_of_pos hσ)).mpr
    linarith [hp.2.2]

end Yau.NodeProofs.F01Aux
