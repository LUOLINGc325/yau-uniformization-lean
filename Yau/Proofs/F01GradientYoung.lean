import spec.CHAIN.CONTRACTS

/-! The numerical Young estimate used to absorb the actual gradient term
into half of the strictly concave penalty's second derivative. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

theorem gradient_young_half {A B c d : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 < d) :
    2 * c * Real.sqrt A * Real.sqrt B ≤ d / 2 * B + (2 * c ^ 2 / d) * A := by
  have hexpand : (d * Real.sqrt B - 2 * c * Real.sqrt A) ^ 2 =
      d ^ 2 * B - 4 * d * c * Real.sqrt A * Real.sqrt B + 4 * c ^ 2 * A := by
    rw [sub_sq, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
    ring
  have hsq := sq_nonneg (d * Real.sqrt B - 2 * c * Real.sqrt A)
  rw [hexpand] at hsq
  calc
    _ ≤ (d ^ 2 * B + 4 * c ^ 2 * A) / (2 * d) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * d)).mpr
      nlinarith
    _ = _ := by field_simp; ring

end Yau.NodeProofs.F01Aux
