import Mathlib
import Yau.Blueprint.ParabolicSpaces

/-! The actual closed-time projection is a contraction, and the kernel's
literal Holder weight controls a fixed power of parabolic distance. -/

open Set
noncomputable section
namespace Yau.LeafProofs.L17SourceLocalizationAux

def timeClamp (T : ℝ) (hT : 0 ≤ T) (τ : ℝ) : Icc (0 : ℝ) T := projIcc 0 T hT τ

theorem timeClamp_continuous (T : ℝ) (hT : 0 ≤ T) : Continuous (timeClamp T hT) := continuous_projIcc (h := hT)

theorem timeClamp_of_mem (T : ℝ) (hT : 0 ≤ T) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) :
    (timeClamp T hT τ : ℝ) = τ := by
  rw [timeClamp, projIcc_of_mem hT hτ]

theorem timeClamp_abs_sub_le (T : ℝ) (hT : 0 ≤ T) (τ σ : ℝ) :
    |(timeClamp T hT σ : ℝ) - (timeClamp T hT τ : ℝ)| ≤ |σ - τ| :=
  Set.abs_projIcc_sub_projIcc hT

theorem timeClamp_sqrt_abs_sub_le (T : ℝ) (hT : 0 ≤ T) (τ σ : ℝ) :
    Real.sqrt |(timeClamp T hT σ : ℝ) - (timeClamp T hT τ : ℝ)| ≤ Real.sqrt |σ - τ| :=
  Real.sqrt_le_sqrt (timeClamp_abs_sub_le T hT τ σ)

theorem add_rpow_le_two_rpow_sum {a b γ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ : 0 ≤ γ) :
    (a + b) ^ γ ≤ (2 : ℝ) ^ γ * (a ^ γ + b ^ γ) := by
  have hm : 0 ≤ max a b := le_trans ha (le_max_left a b)
  have hsum : a + b ≤ 2 * max a b := by linarith [le_max_left a b, le_max_right a b]
  have hmax : (max a b) ^ γ ≤ a ^ γ + b ^ γ := by
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab]
      exact le_add_of_nonneg_left (Real.rpow_nonneg ha _)
    · rw [max_eq_left hba]
      exact le_add_of_nonneg_right (Real.rpow_nonneg hb _)
  calc
    _ ≤ (2 * max a b) ^ γ := Real.rpow_le_rpow (add_nonneg ha hb) hsum hγ
    _ = (2 : ℝ) ^ γ * (max a b) ^ γ := Real.mul_rpow (by norm_num) hm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmax (Real.rpow_nonneg (by norm_num) _)

theorem parabolicDistance_rpow_le_holderWeight {n : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    (p q : Yau.Parabolic.Point n) :
    Yau.Parabolic.parabolicDistance p q ^ γ ≤
      (2 : ℝ) ^ γ * Yau.Parabolic.holderWeight γ p q := by
  have hh := add_rpow_le_two_rpow_sum (norm_nonneg (p.1 - q.1))
    (Real.sqrt_nonneg |p.2 - q.2|) hγ
  have hRoot : (Real.sqrt |p.2 - q.2|) ^ γ = |p.2 - q.2| ^ (γ / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  simpa only [Yau.Parabolic.parabolicDistance, Yau.Parabolic.holderWeight, hRoot] using hh

end Yau.LeafProofs.L17SourceLocalizationAux
