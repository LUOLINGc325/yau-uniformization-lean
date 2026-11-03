import spec.CHAIN.LeafObligations

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

/-- Real linearity is extracted from H2, rather than imposed as a new field. -/
def chuTransformLinear {n : ℕ} {T : Sym n → Point n → Sym n} {K β : ℝ}
    (hT : ChuH2 T K β) (p : Point n) (hp : p ∈ backward 1) : Sym n →ₗ[ℝ] Sym n where
  toFun A := T A p
  map_add' A B := hT.2.1 p hp A B
  map_smul' c A := hT.2.2.1 p hp c A

/-- The inhomogeneous H2 variation bound becomes homogeneous by testing a
unit matrix. This removes the artificial additive constant for all inputs. -/
theorem chuTransform_variation {n : ℕ} {T : Sym n → Point n → Sym n} {K β : ℝ}
    (hT : ChuH2 T K β) (A : Sym n) (p : Point n) (hp : p ∈ backward 1)
    (q : Point n) (hq : q ∈ backward 1) :
    ‖T A p - T A q‖ ≤ 2 * K * ‖A‖ * holderWeight β p q := by
  by_cases hA : A = 0
  · subst A
    have hp0 := (chuTransformLinear hT p hp).map_zero
    have hq0 := (chuTransformLinear hT q hq).map_zero
    change T 0 p = 0 at hp0
    change T 0 q = 0 at hq0
    simp [hp0, hq0]
  have hn : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hunit : ‖(‖A‖⁻¹ : ℝ) • A‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hb := hT.1 ((‖A‖⁻¹ : ℝ) • A) p hp q hq
  rw [hunit, hT.2.2.1 p hp, hT.2.2.1 q hq, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)] at hb
  have hc := mul_le_mul_of_nonneg_left hb hn.le
  have hid : ‖A‖ * (‖A‖⁻¹ * ‖T A p - T A q‖) = ‖T A p - T A q‖ := by
    rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  rw [hid] at hc
  nlinarith

end Yau.LeafProofs.L05Aux
