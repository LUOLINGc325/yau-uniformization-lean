import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

namespace Yau.LeafProofs.L14Aux

variable {E₁ E₂ : Type*}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂]

/-- The cutoff pairing identity, transported through the self-adjoint cutoff. -/
theorem cutoff_energy_identity
    (T : E₁ →L[ℂ] E₁) (C : E₂ →L[ℂ] E₁) (b : E₁) (w : E₂)
    (hT : ∀ x y, inner ℂ x (T y) = inner ℂ (T x) y)
    (hpair : (inner ℂ b (T (T b) - (2 : ℂ) • T (C w))).re = 0) :
    ‖T b‖ ^ 2 = 2 * (inner ℂ (T b) (C w)).re := by
  rw [inner_sub_right, inner_smul_right, hT b (T b), hT b (C w)] at hpair
  have hself : (inner ℂ (T b) (T b)).re = ‖T b‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (T b)
  rw [Complex.sub_re, Complex.mul_re, hself] at hpair
  norm_num at hpair
  linarith

/-- Cauchy--Schwarz converts the cutoff pairing identity into a norm estimate. -/
theorem cutoff_energy_norm_le
    (T : E₁ →L[ℂ] E₁) (C : E₂ →L[ℂ] E₁) (b : E₁) (w : E₂)
    (hT : ∀ x y, inner ℂ x (T y) = inner ℂ (T x) y)
    (hpair : (inner ℂ b (T (T b) - (2 : ℂ) • T (C w))).re = 0) :
    ‖T b‖ ≤ 2 * ‖C w‖ := by
  have hid := cutoff_energy_identity T C b w hT hpair
  have hCS : (inner ℂ (T b) (C w)).re ≤ ‖T b‖ * ‖C w‖ :=
    re_inner_le_norm (𝕜 := ℂ) (T b) (C w)
  by_cases hzero : ‖T b‖ = 0
  · simpa only [hzero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg (C w))
  · have hpos : 0 < ‖T b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith

/-- Squared cutoff estimate before inserting the contraction bound. -/
theorem cutoff_energy_norm_sq_le
    (T : E₁ →L[ℂ] E₁) (C : E₂ →L[ℂ] E₁) (b : E₁) (w : E₂)
    (hT : ∀ x y, inner ℂ x (T y) = inner ℂ (T x) y)
    (hpair : (inner ℂ b (T (T b) - (2 : ℂ) • T (C w))).re = 0) :
    ‖T b‖ ^ 2 ≤ 4 * ‖C w‖ ^ 2 := by
  have hn := cutoff_energy_norm_le T C b w hT hpair
  nlinarith [sq_nonneg (‖T b‖ - 2 * ‖C w‖), norm_nonneg (T b), norm_nonneg (C w)]

/-- Generic cutoff energy estimate with the contraction bound inserted. -/
theorem cutoff_energy_estimate
    (T : E₁ →L[ℂ] E₁) (C : E₂ →L[ℂ] E₁) (b : E₁) (w : E₂) (K : ℝ)
    (hT : ∀ x y, inner ℂ x (T y) = inner ℂ (T x) y)
    (hpair : (inner ℂ b (T (T b) - (2 : ℂ) • T (C w))).re = 0)
    (_hK : 0 ≤ K) (hC : ‖C w‖ ^ 2 ≤ K * ‖w‖ ^ 2) :
    ‖T b‖ ^ 2 ≤ 4 * K * ‖w‖ ^ 2 := by
  have hs := cutoff_energy_norm_sq_le T C b w hT hpair
  nlinarith

/-- The gradient contraction constant `2 * A` gives the cutoff constant `8 * A`. -/
theorem cutoff_energy_estimate_of_two_mul
    (T : E₁ →L[ℂ] E₁) (C : E₂ →L[ℂ] E₁) (b : E₁) (w : E₂) (A : ℝ)
    (hT : ∀ x y, inner ℂ x (T y) = inner ℂ (T x) y)
    (hpair : (inner ℂ b (T (T b) - (2 : ℂ) • T (C w))).re = 0)
    (hA : 0 ≤ A) (hC : ‖C w‖ ^ 2 ≤ 2 * A * ‖w‖ ^ 2) :
    ‖T b‖ ^ 2 ≤ 8 * A * ‖w‖ ^ 2 := by
  have h := cutoff_energy_estimate T C b w (2 * A) hT hpair (by positivity) hC
  nlinarith

end Yau.LeafProofs.L14Aux
