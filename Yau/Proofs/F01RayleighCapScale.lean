import Yau.Proofs.F01UniformRayleighCap

/-! The absorbed Rayleigh exponent has an explicit bound that is uniform
over all comparison intervals below the fixed time scale. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

theorem absorbed_quotient_le_twice {q r : ℝ} (hq : q ≤ 1 / 2)
    (hr : 0 ≤ r) : r / (1 - q) ≤ 2 * r := by
  have hd : 0 < 1 - q := by linarith
  apply (div_le_iff₀ hd).mpr
  nlinarith

theorem absorbed_rayleigh_exponent_le {n : ℕ} {L D T M : ℝ}
    (hL : 0 < L) (hT : 0 ≤ T) (hTD : T ≤ D) (hM : 0 ≤ M)
    (hscale : 4 * (n : ℝ) * D ≤ L) :
    (2 * L⁻¹ * (D * M + (n : ℝ) * T)) /
        (1 - 2 * L⁻¹ * (n : ℝ) * D) ≤ 4 * D * (M + n) / L := by
  have hD : 0 ≤ D := hT.trans hTD
  have hq : 2 * L⁻¹ * (n : ℝ) * D ≤ 1 / 2 := by
    have he : (2 * L⁻¹ * (n : ℝ) * D) * L = 2 * (n : ℝ) * D := by
      field_simp
    nlinarith
  have hr : 0 ≤ 2 * L⁻¹ * (D * M + (n : ℝ) * T) := by positivity
  calc
    _ ≤ 2 * (2 * L⁻¹ * (D * M + (n : ℝ) * T)) :=
      absorbed_quotient_le_twice hq hr
    _ ≤ 4 * D * (M + n) / L := by
      have hN : D * M + (n : ℝ) * T ≤ D * (M + n) := by
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have he : 4 * D * (M + n) / L = 4 * L⁻¹ * (D * (M + n)) := by ring
      rw [he]
      nlinarith [mul_nonneg (inv_nonneg.mpr hL.le) (sub_nonneg.mpr hN)]

theorem absorbed_rayleigh_coefficient_lt_one {n : ℕ} {L D : ℝ}
    (hL : 0 < L) (hscale : 4 * (n : ℝ) * D ≤ L) :
    2 * L⁻¹ * (n : ℝ) * D < 1 := by
  have he : (2 * L⁻¹ * (n : ℝ) * D) * L = 2 * (n : ℝ) * D := by
    field_simp
  nlinarith

end Yau.NodeProofs.F01Aux
