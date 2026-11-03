import Yau.Proofs.V03FourierRapidDecay
import Mathlib.Analysis.PSeries

/-! Every polynomially weighted positive Fourier coefficient sequence of
an actual smooth periodic trace is absolutely summable. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem circleFourier_pos_weighted_summable {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hp : Function.Periodic u (2 * Real.pi)) (m : ℕ) :
    Summable (fun n : ℕ => (n : ℝ) ^ m * ‖circleFourier u (n : ℤ)‖) := by
  obtain ⟨C, hC0, hC⟩ := circleFourier_rapid_decay hu hp (m + 2)
  have hs0 : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)
  have hs : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * C)) :=
    ((summable_nat_add_iff 1).mpr hs0).mul_right C
  rw [← summable_nat_add_iff 1]
  apply Summable.of_norm_bounded hs
  intro n
  have hr : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hk : ((n + 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hb := hC ((n + 1 : ℕ) : ℤ) hk
  have hb' : ‖circleFourier u ((n + 1 : ℕ) : ℤ)‖ ≤
      ((((n + 1 : ℕ) : ℝ) ^ (m + 2))⁻¹ * C) := by
    simpa only [Int.cast_natCast, abs_of_nonneg hr.le, inv_pow] using hb
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    (((n + 1 : ℕ) : ℝ) ^ m * ‖circleFourier u ((n + 1 : ℕ) : ℤ)‖) ≤
        ((n + 1 : ℕ) : ℝ) ^ m * ((((n + 1 : ℕ) : ℝ) ^ (m + 2))⁻¹ * C) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * C := by
      rw [pow_add]
      field_simp [hr.ne']

end Yau.Blueprint.V03Proof
