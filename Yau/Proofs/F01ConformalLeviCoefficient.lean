import Yau.Proofs.F01ConformalBounds

/-! The fixed profile controls both terms in the actual Levi chain rule.
The factor 1/u is treated using the vanishing region, before choosing L. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Yau.NodeProofs.F01Aux

theorem conformalProfile_deriv_zero_of_small {v : ℝ} (hv : v < 1 / 2) :
    deriv conformalProfile v = 0 := by
  have he : conformalProfile =ᶠ[𝓝 v] (fun _ : ℝ => 0) := by
    filter_upwards [Iio_mem_nhds hv] with w hw
    exact conformalProfile_zero hw.le
  rw [he.deriv_eq, deriv_const]

theorem conformalProfile_weighted_derivative_separate {B v : ℝ}
    (hb : Real.exp (-conformalProfile v) *
      (|deriv (deriv conformalProfile) v| + |deriv conformalProfile v|) ≤ B) :
    Real.exp (-conformalProfile v) * |deriv conformalProfile v| ≤ B ∧
    Real.exp (-conformalProfile v) * |deriv (deriv conformalProfile) v| ≤ B := by
  have he := Real.exp_pos (-conformalProfile v)
  constructor <;> nlinarith [abs_nonneg (deriv conformalProfile v),
    abs_nonneg (deriv (deriv conformalProfile) v)]

theorem conformalProfile_weighted_first_div_argument {B v : ℝ} (hB : 0 ≤ B)
    (hb : Real.exp (-conformalProfile v) * |deriv conformalProfile v| ≤ B) :
    Real.exp (-conformalProfile v) * |deriv conformalProfile v| / v ≤ 2 * B := by
  by_cases hs : v < 1 / 2
  · rw [conformalProfile_deriv_zero_of_small hs, abs_zero, mul_zero, zero_div]
    positivity
  · have hv : 0 < v := by linarith
    apply (div_le_iff₀ hv).mpr
    have hBv : B ≤ 2 * B * v := by
      nlinarith [mul_nonneg hB (show 0 ≤ 2 * v - 1 by linarith)]
    exact hb.trans hBv

theorem conformalProfile_uniform_levi_coefficients :
    ∃ B : ℝ, 0 < B ∧ ∀ L r : ℝ, 0 < L → 0 < r → r < L →
      Real.exp (-conformalProfile (r / L)) *
        (|deriv conformalProfile (r / L)| / (L * r) +
          |deriv (deriv conformalProfile) (r / L)| / L ^ 2) ≤ B / L ^ 2 := by
  obtain ⟨C, hC, hc⟩ := conformalProfile_weighted_derivative_bounds
  refine ⟨3 * C, by positivity, ?_⟩
  intro L r hL hr hrl
  have hs := conformalProfile_weighted_derivative_separate
    (hc (r / L) ⟨(div_pos hr hL).le, (div_lt_one hL).mpr hrl⟩).2
  have hf := conformalProfile_weighted_first_div_argument hC.le hs.1
  have he : Real.exp (-conformalProfile (r / L)) *
      (|deriv conformalProfile (r / L)| / (L * r) +
        |deriv (deriv conformalProfile) (r / L)| / L ^ 2) =
      (Real.exp (-conformalProfile (r / L)) * |deriv conformalProfile (r / L)| / (r / L) +
        Real.exp (-conformalProfile (r / L)) * |deriv (deriv conformalProfile) (r / L)|) /
          L ^ 2 := by
    field_simp [hL.ne', hr.ne']
    <;> ring
  rw [he]
  exact div_le_div_of_nonneg_right (by linarith [hs.2]) (sq_nonneg L)

end Yau.NodeProofs.F01Aux
