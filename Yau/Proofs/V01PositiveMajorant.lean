import Yau.Proofs.V01CanonicalCost
import Mathlib.Analysis.Matrix.Order

/-! V01 scratch source: turn the actual frame-center inequality into a
positive majorant in fixed coordinates, with its exact symplectic cost. -/

noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder

namespace Yau.Blueprint.V01Proof

variable {n : ℕ}

theorem unscale_posSemidef_sub {B W : CotangentMatrix n} {a b : ℝ}
    (hb : 0 < b) (h : ((a : ℂ) • B - (b : ℂ) • W).PosSemidef) :
    (((a / b : ℝ) : ℂ) • B - W).PosSemidef := by
  have hscale : 0 ≤ ((b⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast inv_nonneg.mpr hb.le
  have ha : ((b⁻¹ : ℝ) : ℂ) * (a : ℂ) = ((a / b : ℝ) : ℂ) := by
    push_cast
    rw [div_eq_mul_inv, mul_comm]
  have hb' : ((b⁻¹ : ℝ) : ℂ) * (b : ℂ) = 1 := by
    exact_mod_cast inv_mul_cancel₀ hb.ne'
  simpa only [smul_sub, smul_smul, ha, hb', one_smul] using h.smul hscale

theorem inverse_congruence_majorant {B W S : CotangentMatrix n}
    (hS : IsUnit S) (h : (B - Sᴴ * W * S).PosSemidef) :
    (S⁻¹ᴴ * B * S⁻¹ - W).PosSemidef := by
  have hSS : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS)
  have hcancel : S⁻¹ᴴ * (Sᴴ * W * S) * S⁻¹ = W := by
    calc
      _ = (S * S⁻¹)ᴴ * W * (S * S⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = W := by rw [hSS, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hp := h.conjTranspose_mul_mul_same S⁻¹
  simpa only [Matrix.mul_sub, Matrix.sub_mul, hcancel] using hp

def fixedPositiveMajorant (H S : CotangentMatrix n) (r h₀ : ℝ) : CotangentMatrix n :=
  (((1 + r) / h₀ ^ 2 : ℝ) : ℂ) • (S⁻¹ᴴ * (Hᴴ * H) * S⁻¹)

theorem fixedPositiveMajorant_posDef {H S : CotangentMatrix n}
    (hH : IsUnit H) (hS : IsUnit S) {r h₀ : ℝ} (hr : 0 ≤ r) (hh₀ : 0 < h₀) :
    (fixedPositiveMajorant H S r h₀).PosDef := by
  have hG : (Hᴴ * H).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self H (Matrix.mulVec_injective_iff_isUnit.mpr hH)
  have hSinv : IsUnit S⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hS
  have hcong : (S⁻¹ᴴ * (Hᴴ * H) * S⁻¹).PosDef :=
    hG.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hSinv)
  exact hcong.smul (by exact_mod_cast div_pos (by linarith : 0 < 1 + r) (sq_pos_of_pos hh₀))

theorem fixedPositiveMajorant_ge {H S W : CotangentMatrix n}
    (hS : IsUnit S) {r h₀ : ℝ} (hh₀ : 0 < h₀)
    (hcenter : (((1 + r : ℝ) : ℂ) • (Hᴴ * H) -
      ((h₀ ^ 2 : ℝ) : ℂ) • (Sᴴ * W * S)).PosSemidef) :
    (fixedPositiveMajorant H S r h₀ - W).PosSemidef := by
  have hunscale := unscale_posSemidef_sub (sq_pos_of_pos hh₀) hcenter
  have hfixed := inverse_congruence_majorant hS hunscale
  simpa only [fixedPositiveMajorant, Matrix.mul_smul, Matrix.smul_mul] using hfixed

theorem fixedPositiveMajorant_symplectic_cost {H S : CotangentMatrix n}
    (hH : IsUnit H) (hS : IsUnit S) {r h₀ : ℝ} (hr : 0 ≤ r) (hh₀ : 0 < h₀) :
    symplecticP (fixedPositiveMajorant H S r h₀) =
      ((1 + r) / h₀ ^ 2) ^ 2 * bivectorCost (Hᴴ * H) (frameBivector S) := by
  rw [← bivectorCost_canonical _ (fixedPositiveMajorant_posDef hH hS hr hh₀).isHermitian]
  rw [fixedPositiveMajorant, bivectorCost_real_smul, bivectorCost_congruence]
  rfl

end Yau.Blueprint.V01Proof
