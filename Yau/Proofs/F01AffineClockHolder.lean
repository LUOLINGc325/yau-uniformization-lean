import Yau.Proofs.F01ClampedAffineHolder
import Yau.Proofs.F01HolderBilinear

/-! Affine clock profiles have one parabolic Holder budget before
both their bounded center and bounded slope. This is the positive-time
analogue of the initial clamped profile. -/
noncomputable section
open Set Metric
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem affine_clock_holder_budget {T β : ℝ} (hT : 0 ≤ T) (hβ : β ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (τ κ : ℝ), |τ| ≤ T → |κ| ≤ 1 →
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1) (fun p => τ + κ * p.2) K := by
  let P := (2 : ℝ) ^ (1 - β / 2)
  let K := 1 + T + P
  have hP : 0 ≤ P := Real.rpow_nonneg (by norm_num) _
  have hK : 0 < K := by dsimp only [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro τ κ hτ hκ
  refine ⟨hK.le, ?_, ?_⟩
  · intro p hp
    have ht : |p.2| ≤ 1 := abs_le.mpr ⟨hp.2.1, hp.2.2⟩
    have hMul : |κ * p.2| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul hκ ht (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    have hAdd : |τ + κ * p.2| ≤ |τ| + |κ * p.2| := by
      simpa only [Real.norm_eq_abs] using norm_add_le τ (κ * p.2)
    rw [Real.norm_eq_abs]
    exact hAdd.trans (by dsimp only [K]; linarith)
  · intro p hp q hq
    have he : |p.2 - q.2| ≤ 2 := by
      apply abs_le.mpr
      constructor <;> linarith [hp.2.1, hp.2.2, hq.2.1, hq.2.2]
    have hPower := linear_le_bounded_holder_power (abs_nonneg (p.2 - q.2))
      (by norm_num : (0 : ℝ) < 2) he (by linarith : β / 2 ≤ 1)
    have hPK : P ≤ K := by dsimp only [K]; linarith
    have hDiff : ‖τ + κ * p.2 - (τ + κ * q.2)‖ ≤ |p.2 - q.2| := by
      rw [show τ + κ * p.2 - (τ + κ * q.2) = κ * (p.2 - q.2) by ring,
        Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) hκ)
    calc
      _ ≤ |p.2 - q.2| := hDiff
      _ ≤ P * |p.2 - q.2| ^ (β / 2) := hPower
      _ ≤ K * |p.2 - q.2| ^ (β / 2) :=
        mul_le_mul_of_nonneg_right hPK (Real.rpow_nonneg (abs_nonneg _) _)
      _ ≤ K * holderWeight β p q := by
        unfold holderWeight
        nlinarith [mul_nonneg hK.le (Real.rpow_nonneg (norm_nonneg (p.1 - q.1)) β)]

end Yau.NodeProofs.F01Aux
