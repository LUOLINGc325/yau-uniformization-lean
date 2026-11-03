import Yau.LeafProofs.L17ParabolicC2Scaling
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Actual whole-space Holder bounds under the exact parabolic coordinate rescaling. -/

noncomputable section

open Set

namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic

variable {n : ℕ}

theorem holderWeight_le_two_parabolicDistance_rpow {α : ℝ} (hα : 0 ≤ α) (p q : Point n) :
    holderWeight α p q ≤ 2 * parabolicDistance p q ^ α := by
  have ht : |p.2 - q.2| ^ (α / 2) = (Real.sqrt |p.2 - q.2|) ^ α := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  have hx := Real.rpow_le_rpow (norm_nonneg (p.1 - q.1))
    (le_add_of_nonneg_right (Real.sqrt_nonneg |p.2 - q.2|)) hα
  have htime := Real.rpow_le_rpow (Real.sqrt_nonneg |p.2 - q.2|)
    (le_add_of_nonneg_left (norm_nonneg (p.1 - q.1))) hα
  dsimp [holderWeight]
  rw [ht]
  dsimp [parabolicDistance]
  linarith

theorem parabolicDistance_scalePoint {ρ : ℝ} (hρ : 0 < ρ) (p q : Point n) :
    parabolicDistance (parabolicScalePoint ρ p) (parabolicScalePoint ρ q) =
      parabolicDistance p q / ρ := by
  have hsq : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  change ‖ρ⁻¹ • p.1 - ρ⁻¹ • q.1‖ +
      Real.sqrt |(ρ ^ 2)⁻¹ * p.2 - (ρ ^ 2)⁻¹ * q.2| =
    (‖p.1 - q.1‖ + Real.sqrt |p.2 - q.2|) / ρ
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ),
    ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hsq),
    Real.sqrt_mul (inv_nonneg.mpr hsq.le), Real.sqrt_inv, Real.sqrt_sq hρ.le]
  ring

theorem holderBound_scaled_difference
    {V : Type*} [NormedAddCommGroup V] {ρ T α C : ℝ} (hρ : 0 < ρ) (hα : 0 ≤ α)
    {f : Point n → V} (hf : HolderBound α (cylinder Set.univ 0 (T / ρ ^ 2)) f C)
    {p q : Point n} (hp : p ∈ cylinder Set.univ 0 T) (hq : q ∈ cylinder Set.univ 0 T) :
    ‖f (parabolicScalePoint ρ p) - f (parabolicScalePoint ρ q)‖ ≤
      2 * C * (parabolicDistance p q / ρ) ^ α := by
  have hleft := parabolicScalePoint_mem_cylinder hρ.ne' hp
  have hright := parabolicScalePoint_mem_cylinder hρ.ne' hq
  calc
    _ ≤ C * holderWeight α (parabolicScalePoint ρ p) (parabolicScalePoint ρ q) :=
      hf.2.2 _ hleft _ hright
    _ ≤ C * (2 * parabolicDistance (parabolicScalePoint ρ p) (parabolicScalePoint ρ q) ^ α) :=
      mul_le_mul_of_nonneg_left (holderWeight_le_two_parabolicDistance_rpow hα _ _) hf.1
    _ = _ := by rw [parabolicDistance_scalePoint hρ]; ring

end Yau.LeafProofs.L17Aux
