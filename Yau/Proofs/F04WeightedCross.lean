import Yau.Proofs.F04CrossMatrix

open scoped Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

def scaleCovector {n : ℕ} (r : ℝ) (c : Fin n → ℂ) : Fin n → ℂ := (r : ℂ) • c

theorem dual_norm_scale {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ) (r : ℝ) :
    dualNormMat G (WithLp.toLp 2 (scaleCovector r c)) = r ^ 2 * dualNormMat G (WithLp.toLp 2 c) := by
  change (star ((r : ℂ) • c) ⬝ᵥ ((G⁻¹)ᵀ *ᵥ ((r : ℂ) • c))).re =
    r ^ 2 * (star c ⬝ᵥ ((G⁻¹)ᵀ *ᵥ c)).re
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem covectorCross_scale_inv {n : ℕ} (r : ℝ) (hr : r ≠ 0) (c d : Fin n → ℂ) :
    covectorCross (scaleCovector r c) (scaleCovector r⁻¹ d) = covectorCross c d := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  ext i j
  simp only [covectorCross, scaleCovector, Matrix.add_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Pi.smul_apply, star_mul, Complex.star_def, Complex.conj_ofReal,
    smul_eq_mul]
  simp only [Complex.ofReal_inv]
  field_simp [hrC]

theorem weighted_covector_cross_bound {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef)
    (c d : Fin n → ℂ) (r : ℝ) (hr : r ≠ 0) :
    let q := r ^ 2 * dualNormMat G (WithLp.toLp 2 c) +
      r⁻¹ ^ 2 * dualNormMat G (WithLp.toLp 2 d)
    HermLE (((-q : ℝ) : ℂ) • G) (covectorCross c d) ∧
      HermLE (covectorCross c d) ((q : ℂ) • G) := by
  have hh := covector_cross_bound G hG (scaleCovector r c) (scaleCovector r⁻¹ d)
  dsimp only at hh
  rw [dual_norm_scale, dual_norm_scale, covectorCross_scale_inv r hr c d] at hh
  exact hh

end Yau.F04Proof
