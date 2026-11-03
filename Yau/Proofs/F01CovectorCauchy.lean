import spec.CHAIN.CONTRACTS

/-! Cauchy--Schwarz in the original column convention. The cotangent
quadratic form uses the transpose of the inverse, exactly as dualNormMat. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem matrix_covector_cauchy (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (ξ v : Fin n → ℂ) :
    Complex.normSq (ξ ⬝ᵥ v) ≤
      (star ξ ⬝ᵥ ((H⁻¹)ᵀ *ᵥ ξ)).re * (star v ⬝ᵥ (H *ᵥ v)).re := by
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  let w : Fin n → ℂ := H⁻¹ *ᵥ star ξ
  have hp (q : Fin n → ℂ) : star w ⬝ᵥ (H *ᵥ q) = ξ ⬝ᵥ q := by
    dsimp [w]
    rw [Matrix.star_mulVec, star_star, hH.inv.isHermitian.eq,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hw : star w ⬝ᵥ (H *ᵥ w) = star ξ ⬝ᵥ ((H⁻¹)ᵀ *ᵥ ξ) := by
    rw [hp]
    exact (Matrix.dotProduct_transpose_mulVec H⁻¹ (star ξ) ξ).symm
  have hcs := hH.star_dotProduct_mulVec_mul_le w v
  change star (star w ⬝ᵥ (H *ᵥ v)) * (star w ⬝ᵥ (H *ᵥ v)) ≤
    (star w ⬝ᵥ (H *ᵥ w)) * (star v ⬝ᵥ (H *ᵥ v)) at hcs
  rw [hp, hw] at hcs
  have hr := (Complex.le_def.mp hcs).1
  have him : (star v ⬝ᵥ (H *ᵥ v)).im = 0 :=
    (Complex.nonneg_iff.mp (hH.posSemidef.dotProduct_mulVec_nonneg v)).2.symm
  simpa only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    him, mul_zero, sub_zero, neg_mul, sub_neg_eq_add, Complex.normSq_apply] using hr

theorem dualNormMat_cauchy (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (ξ v : ComplexVector n) :
    ‖WithLp.ofLp ξ ⬝ᵥ WithLp.ofLp v‖ ^ 2 ≤
      dualNormMat H ξ * (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re := by
  simpa only [Complex.sq_norm, dualNormMat] using
    matrix_covector_cauchy H hH (WithLp.ofLp ξ) (WithLp.ofLp v)

end Yau.NodeProofs.F01Aux
