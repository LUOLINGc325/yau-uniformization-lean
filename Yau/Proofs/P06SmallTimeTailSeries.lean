import Yau.Proofs.P06CutoffTailSeries

/-! The Gaussian is retained while the remote dyadic shells are summed. -/
noncomputable section
open Filter Finset
open scoped Topology

namespace Yau.NodeProofs.P06Aux.SmallTimeTail
open CutoffTail

theorem radius_add (J q : ℕ) : radius (J + q) = radius J * radius q := by
  exact pow_add _ _ _

/-- Split one shell Gaussian into a uniform small-time factor and a fixed
summable Gaussian in the relative shell index. -/
theorem gaussian_le_split {A τ t r R Q : ℝ}
    (hA : 0 < A) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (ht : 0 < t) (htτ : t ≤ 2 * τ)
    (hR : 1 ≤ R) (hQ : 1 ≤ Q) (hsep : 2 * r ≤ R * Q) :
    Real.exp (-(R * Q - r) ^ 2 / (2 * A ^ 2 * t)) ≤
      Real.exp (-R ^ 2 / (32 * A ^ 2 * τ)) *
        Real.exp (-Q ^ 2 / (32 * A ^ 2)) := by
  have hR0 : 0 ≤ R := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hQ2 : 1 ≤ Q ^ 2 := by nlinarith
  have hgap : R ^ 2 * Q ^ 2 ≤ 4 * (R * Q - r) ^ 2 := by
    have hRQ : 0 ≤ R * Q := mul_nonneg hR0 hQ0
    nlinarith [sq_nonneg (R * Q - 2 * r)]
  have h₁ : R ^ 2 ≤ R ^ 2 * Q ^ 2 := by nlinarith
  have h₂ : τ * Q ^ 2 ≤ R ^ 2 * Q ^ 2 := by
    exact mul_le_mul_of_nonneg_right (hτ1.trans hR2) (sq_nonneg Q)
  have hsplit : R ^ 2 + τ * Q ^ 2 ≤ 2 * (R ^ 2 * Q ^ 2) := by linarith
  have htime : (R ^ 2 + τ * Q ^ 2) * t ≤
      4 * τ * (R ^ 2 * Q ^ 2) := by
    calc
      _ ≤ (2 * (R ^ 2 * Q ^ 2)) * t :=
        mul_le_mul_of_nonneg_right hsplit ht.le
      _ ≤ (2 * (R ^ 2 * Q ^ 2)) * (2 * τ) :=
        mul_le_mul_of_nonneg_left htτ (by positivity)
      _ = _ := by ring
  have hfinal : (R ^ 2 + τ * Q ^ 2) * t ≤
      16 * τ * (R * Q - r) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 4 * τ)
    nlinarith
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hden : 0 < 2 * A ^ 2 * t := by positivity
  have hdenτ : 0 < 32 * A ^ 2 * τ := by positivity
  have he : (R ^ 2 + τ * Q ^ 2) / (32 * A ^ 2 * τ) ≤
      (R * Q - r) ^ 2 / (2 * A ^ 2 * t) := by
    apply (div_le_div_iff₀ hdenτ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hfinal (by positivity : 0 ≤ 2 * A ^ 2)
    nlinarith
  convert neg_le_neg he using 1 <;> field_simp <;> ring

def shellMajorant (d : ℕ) (A : ℝ) (q : ℕ) : ℝ :=
  radius q ^ d * Real.exp (-radius q ^ 2 / (32 * A ^ 2))

theorem shellMajorant_nonneg (d : ℕ) (A : ℝ) (q : ℕ) :
    0 ≤ shellMajorant d A q := by
  unfold shellMajorant
  exact mul_nonneg (pow_nonneg (radius_pos q).le d) (Real.exp_pos _).le

theorem summable_shellMajorant (d : ℕ) {A : ℝ} (hA : 0 < A) :
    Summable (shellMajorant d A) := by
  have ha : 0 < 1 / (32 * A ^ 2) := by positivity
  refine Summable.of_nonneg_of_le (shellMajorant_nonneg d A) ?_
    (summable_dyadic d ha)
  intro q
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (radius_pos q).le d)
  apply Real.exp_le_exp.mpr
  have hQ := one_le_radius q
  have hsq : radius q ≤ radius q ^ 2 := by nlinarith
  have hh := div_le_div_of_nonneg_right hsq (by positivity : 0 ≤ 32 * A ^ 2)
  convert neg_le_neg hh using 1 <;> ring

theorem shellMajorant_tsum_nonneg (d : ℕ) (A : ℝ) :
    0 ≤ ∑' q, shellMajorant d A q :=
  tsum_nonneg (shellMajorant_nonneg d A)

end Yau.NodeProofs.P06Aux.SmallTimeTail
