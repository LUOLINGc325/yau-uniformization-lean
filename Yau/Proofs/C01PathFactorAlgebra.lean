import Yau.Proofs.C01PathScalarJets

/-! The multiplicative path argument uses the nonnegative scalar
curvature itself.  No logarithm or strictly positive scalar is required. -/

noncomputable section

namespace Yau.NodeProofs.C01Aux

theorem scalar_clock_harnack_algebra (R Rₜ G q t a b : ℝ)
    (ht : 0 < t) (ha : 0 < a) (hR : 0 ≤ R)
    (hH : 0 ≤ Rₜ + t⁻¹ * R + a⁻¹ * G + (a⁻¹) ^ 2 * R * q)
    (hq : q ≤ a * b) :
    0 ≤ a * R + t * (G + a * Rₜ) + t * R * b := by
  have hs := mul_nonneg (mul_pos ht ha).le hH
  have heq : (t * a) * (Rₜ + t⁻¹ * R + a⁻¹ * G + (a⁻¹) ^ 2 * R * q) =
      a * R + t * (G + a * Rₜ) + t * R * (q / a) := by
    field_simp [ht.ne', ha.ne']
    <;> ring
  rw [heq] at hs
  have hqb : q / a ≤ b := (div_le_iff₀ ha).mpr (by simpa only [mul_comm] using hq)
  have hm := mul_le_mul_of_nonneg_left hqb (mul_nonneg ht.le hR)
  linarith

theorem scalar_integratingFactor_hasDerivAt
    {τ R B : ℝ → ℝ} {s a r b : ℝ}
    (hτ : HasDerivAt τ a s) (hR : HasDerivAt R r s) (hB : HasDerivAt B b s) :
    HasDerivAt (fun u => τ u * R u * Real.exp (B u))
      (Real.exp (B s) * (a * R s + τ s * r + τ s * R s * b)) s := by
  have hd := (hτ.mul hR).mul hB.exp
  convert! hd using 1 <;> simp only [Pi.mul_apply] <;> ring

end Yau.NodeProofs.C01Aux
