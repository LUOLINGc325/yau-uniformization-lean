import Yau.Proofs.F01BoundedAtlasSpaceTimeSmooth
import Yau.Proofs.F01ShiftedNativePotential

/-! Actual normalized profiles give the original manifold potential's
joint smoothness after undoing the same space, time and amplitude scales. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothSpaceTime_of_normalized_terminal_profiles
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (U : M.Carrier → ℝ → ℝ) {σ : ℝ} (hσ : 0 < σ) (hσr : σ ≤ A.radius)
    (T : ℝ) (I : Set ℝ)
    (hProfiles : ∀ a, ContDiffOn ℝ ∞ (shiftedNativePotential A U a σ T)
      (ball 0 (1 / 2) ×ˢ I)) :
    SmoothSpaceTime U {t : ℝ | (t - T) / σ ^ 2 ∈ I} := by
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ.ne'
  apply smoothSpaceTime_of_bounded_atlas_coefficients g hg A (r := σ / 2)
    (by positivity) (by linarith) U
  intro a
  let ψ : Point n → Point n := fun p => (σ⁻¹ • p.1, (p.2 - T) / σ ^ 2)
  have hψ : ContDiff ℝ ∞ ψ := by dsimp only [ψ]; fun_prop
  have hMap : MapsTo ψ
      (ball 0 (σ / 2) ×ˢ {t : ℝ | (t - T) / σ ^ 2 ∈ I}) (ball 0 (1 / 2) ×ˢ I) := by
    intro p hp
    refine ⟨?_, hp.2⟩
    change σ⁻¹ • p.1 ∈ ball (0 : Space n) (1 / 2)
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσ)]
    have hpN : ‖p.1‖ < σ / 2 := by simpa only [mem_ball, dist_zero_right] using hp.1
    calc
      _ < σ⁻¹ * (σ / 2) := mul_lt_mul_of_pos_left hpN (inv_pos.mpr hσ)
      _ = 1 / 2 := by field_simp [hσ.ne']
  have hh : ContDiffOn ℝ ∞ (fun p : Point n => σ ^ 2 * shiftedNativePotential A U a σ T (ψ p))
      (ball 0 (σ / 2) ×ˢ {t : ℝ | (t - T) / σ ^ 2 ∈ I}) :=
    contDiffOn_const.mul ((hProfiles a).comp hψ.contDiffOn hMap)
  apply hh.congr
  intro p hp
  have hClock : T + σ ^ 2 * ((p.2 - T) / σ ^ 2) = p.2 := by field_simp; ring
  simp only [shiftedNativePotential, affineParabolicPotential, affineParabolicPullback,
    affineParabolicPoint, ψ, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul, add_zero, hClock,
    ← mul_assoc, mul_inv_cancel₀ hσ2, one_mul]

end Yau.NodeProofs.F01Aux
