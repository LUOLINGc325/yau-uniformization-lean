import Yau.Proofs.F01ConformalBounds
import Yau.Proofs.F01BoundaryRatio

/-! Exact scalar cancellation in the actual rescaled conformal Gram matrix.
The right side extends across scale zero; each genuine chart uses δ>0. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

theorem conformalProfile_exp_of_large {v : ℝ} (hv : 3 / 4 ≤ v) (h1 : v < 1) :
    Real.exp (conformalProfile v) = ((1 - v) ^ 2)⁻¹ := by
  have hn := conformalProfile_exp_neg hv h1
  rw [Real.exp_neg] at hn
  simpa only [inv_inv] using congrArg (fun a : ℝ => a⁻¹) hn

theorem scaled_conformal_scalar_cancellation {δ R v : ℝ}
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8) (hR : 0 < R) (hRmax : R ≤ 3 / 2)
    (hgap : 1 - v = δ * R) (c : ℝ) :
    (c * δ) ^ 2 * Real.exp (conformalProfile v) = c ^ 2 / R ^ 2 := by
  have h1 : v < 1 := by nlinarith [mul_pos hδ hR]
  have hb : δ * R ≤ (1 / 8 : ℝ) * (3 / 2) :=
    mul_le_mul hδsmall hRmax hR.le (by norm_num)
  have hv : 3 / 4 ≤ v := by nlinarith
  rw [conformalProfile_exp_of_large hv h1, hgap, mul_pow]
  field_simp [hδ.ne', hR.ne'] <;> ring

end Yau.NodeProofs.F01Aux
