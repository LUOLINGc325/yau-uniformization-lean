import spec.CHAIN.CONTRACTS

/-! Uncompiled F01 scratch: the three-halves growth shift is separate from
canonical linear growth. Taking s=sqrt(r) gives the required epsilon^-3
constant without using the canonical epsilon^-1 estimate. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

theorem cubic_quartic_young {c d s : ℝ}
    (hc : 0 ≤ c) (hd : 0 < d) (hs : 0 ≤ s) :
    c * s ^ 3 ≤ d * s ^ 4 + c ^ 4 / d ^ 3 := by
  by_cases hds : d * s ≤ c
  · have hp : (d * s) ^ 3 ≤ c ^ 3 :=
      pow_le_pow_left₀ (mul_nonneg hd.le hs) hds 3
    have hsmall : c * s ^ 3 ≤ c ^ 4 / d ^ 3 := by
      apply (le_div_iff₀ (pow_pos hd 3)).mpr
      calc
        (c * s ^ 3) * d ^ 3 = c * (d * s) ^ 3 := by ring
        _ ≤ c * c ^ 3 := mul_le_mul_of_nonneg_left hp hc
        _ = c ^ 4 := by ring
    exact hsmall.trans (le_add_of_nonneg_left (mul_nonneg hd.le (pow_nonneg hs 4)))
  · have hlarge : c ≤ d * s := (lt_of_not_ge hds).le
    have hp := mul_le_mul_of_nonneg_right hlarge (pow_nonneg hs 3)
    calc
      c * s ^ 3 ≤ d * s ^ 4 := by nlinarith [hp]
      _ ≤ d * s ^ 4 + c ^ 4 / d ^ 3 :=
        le_add_of_nonneg_right (div_nonneg (pow_nonneg hc 4) (pow_pos hd 3).le)

theorem three_halves_shift_polynomial {c d s : ℝ}
    (hc : 0 ≤ c) (hd : 0 < d) (hs : 0 ≤ s) :
    c * (1 + s ^ 3) - d * s ^ 4 ≤ c + c ^ 4 / d ^ 3 := by
  have h := cubic_quartic_young hc hd hs
  nlinarith

end Yau.NodeProofs.F01Aux
