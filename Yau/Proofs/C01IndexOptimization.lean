import Yau.Proofs.C01IndexIntegralBound

/-! Optimizing the cutoff scale gives the linear-in-distance loss
needed for the square-root-time first-exit barrier. The short-distance
case uses the actual pointwise estimate. -/

noncomputable section

namespace Yau.NodeProofs.C01Aux

theorem index_integral_optimized_bound
    (d r B C I : ℝ) (hd : 0 < d) (hr : 0 < r) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hpoint : I ≤ C * (1 + d ^ 2) * d ^ 2 / r ^ 2)
    (hindex : ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 2 →
      I ≤ B / κ + 2 * κ * C * (1 + d ^ 2) * d ^ 2 / r ^ 2) :
    I / (2 * d) ≤ (B + C + 1) * (1 + d) / r := by
  let A := 1 + d
  have hA : 0 < A := by dsimp only [A]; linarith
  have hsq : 1 + d ^ 2 ≤ A ^ 2 := by dsimp only [A]; nlinarith
  by_cases hshort : d * A ≤ r
  · have hpoly : d * (1 + d ^ 2) ≤ r * A := by
      have H := mul_le_mul_of_nonneg_left hsq hd.le
      have H' := mul_le_mul_of_nonneg_right hshort hA.le
      nlinarith only [H, H']
    have H := (le_div_iff₀ (sq_pos_of_pos hr)).mp hpoint
    have Hp := mul_le_mul_of_nonneg_left hpoly (mul_nonneg hC hd.le)
    have HIr : I * r ≤ C * d * A := by
      apply le_of_mul_le_mul_left (a := r) _ hr
      nlinarith only [H, Hp]
    have Hbound : I / (2 * d) ≤ C * A / (2 * r) :=
      (div_le_div_iff₀ (by positivity : 0 < 2 * d) (by positivity : 0 < 2 * r)).mpr
        (by nlinarith only [HIr])
    calc
      _ ≤ C * A / (2 * r) := Hbound
      _ = (C / 2) * A / r := by ring
      _ ≤ (B + C + 1) * A / r :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) hA.le) hr.le
  · have hlong : r < d * A := lt_of_not_ge hshort
    let κ := r / (2 * d * A)
    have hκ : 0 < κ := div_pos hr (by positivity)
    have hκhalf : κ ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * d * A)).mpr
      linarith
    have Hi := div_le_div_of_nonneg_right (hindex κ hκ hκhalf) (by positivity : 0 ≤ 2 * d)
    have heq : (B / κ + 2 * κ * C * (1 + d ^ 2) * d ^ 2 / r ^ 2) / (2 * d) =
        B * A / r + C * (1 + d ^ 2) / (2 * A * r) := by
      dsimp only [κ]
      field_simp [hd.ne', hr.ne', hA.ne'] <;> ring
    rw [heq] at Hi
    have Hlast : C * (1 + d ^ 2) / (2 * A * r) ≤ C * A / (2 * r) := by
      calc
        _ ≤ C * A ^ 2 / (2 * A * r) := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq hC) (by positivity)
        _ = _ := by field_simp [hA.ne', hr.ne'] <;> ring
    calc
      _ ≤ B * A / r + C * (1 + d ^ 2) / (2 * A * r) := Hi
      _ ≤ B * A / r + C * A / (2 * r) := add_le_add le_rfl Hlast
      _ = (B + C / 2) * A / r := by ring
      _ ≤ (B + C + 1) * A / r := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hA.le) hr.le

end Yau.NodeProofs.C01Aux
