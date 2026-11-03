import Yau.Proofs.F03DyadicScaleBand
import Yau.Proofs.F03MetricDefectHeatMajorants

/-! Actual fractional exponents and uniform scale comparison on every active dyadic annulus. -/
noncomputable section
namespace Yau.Proofs.F03Aux

theorem heatDecayExponent_lt_one (n : ℕ) : heatDecayExponent n < 1 := by
  have hNat : 3 ≤ 2*n+3 := by omega
  have hCast : (3:ℝ) ≤ ((2*n+3:ℕ):ℝ) := by exact_mod_cast hNat
  have hDen : (1:ℝ) < 2*((2*n+3:ℕ):ℝ) := by linarith
  dsimp [heatDecayExponent]
  exact (div_lt_one (by positivity)).mpr hDen

theorem dyadicScale_rpow_le {s : ℝ} (hs : 1 ≤ s) (j : ℕ)
    (hj : (2:ℝ)^j/2 ≤ s) {α : ℝ} (hα : 0 ≤ α) :
    ((2:ℝ)^j)^α ≤ (2:ℝ)^α*s^α := by
  have hScale : (2:ℝ)^j ≤ 2*s := by linarith
  calc
    _ ≤ (2*s)^α := Real.rpow_le_rpow (by positivity) hScale hα
    _ = _ := Real.mul_rpow (by norm_num) (by linarith)

theorem dyadicScale_inverse_le {s : ℝ} (hs : 1 ≤ s) (j : ℕ)
    (hj : s ≤ 2*(2:ℝ)^j) :
    1/(2:ℝ)^j ≤ 2/s := by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hScale : 0 < (2:ℝ)^j := by positivity
  apply (div_le_div_iff₀ hScale hs0).mpr
  simpa only [one_mul,mul_one,mul_comm] using hj

theorem dyadicScale_derivative_at_value
    {B s : ℝ} (hB : 0 ≤ B) (hs : 1 ≤ s) (j : ℕ)
    (hFirst : |deriv (dyadicPartition j) s| ≤ B/(2:ℝ)^j)
    (hSecond : |deriv (deriv (dyadicPartition j)) s| ≤ B/((2:ℝ)^j)^2) :
    |deriv (dyadicPartition j) s| ≤ 2*B/s ∧
      |deriv (deriv (dyadicPartition j)) s| ≤ 4*B/s^2 := by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  constructor
  · by_cases hZero : deriv (dyadicPartition j) s=0
    · rw [hZero,abs_zero];positivity
    have hInv := dyadicScale_inverse_le hs j (dyadicPartition_deriv_scale_support hs j hZero).2
    calc
      _ ≤ B/(2:ℝ)^j := hFirst
      _ = B*(1/(2:ℝ)^j) := by ring
      _ ≤ B*(2/s) := mul_le_mul_of_nonneg_left hInv hB
      _ = _ := by ring
  · by_cases hZero : deriv (deriv (dyadicPartition j)) s=0
    · rw [hZero,abs_zero];positivity
    have hInv := dyadicScale_inverse_le hs j (dyadicPartition_secondDeriv_scale_support hs j hZero).2
    have hInvSq : (1/(2:ℝ)^j)^2 ≤ (2/s)^2 :=
      pow_le_pow_left₀ (by positivity) hInv 2
    calc
      _ ≤ B/((2:ℝ)^j)^2 := hSecond
      _ = B*(1/(2:ℝ)^j)^2 := by ring
      _ ≤ B*(2/s)^2 := mul_le_mul_of_nonneg_left hInvSq hB
      _ = _ := by ring

end Yau.Proofs.F03Aux
