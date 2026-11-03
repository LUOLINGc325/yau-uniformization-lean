import Yau.Proofs.E01Congruence
import Yau.Proofs.E01QuadraticReal

/-! The conjugated inverse-transpose raising convention of the actual
cotangent norm, without a unit-length normalization. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.Proofs.C03Aux.ChernGauge

open Yau Yau.Blueprint Yau.NodeProofs.E01Aux
variable {n : ℕ}

theorem ellipsoidQuadratic_conjugate (H : Herm n) (v : ComplexVector n) :
    ellipsoidQuadratic H (WithLp.toLp 2 (star (WithLp.ofLp v))) =
      ellipsoidQuadratic Hᵀ v := by
  unfold ellipsoidQuadratic
  apply congrArg Complex.re
  simp only [WithLp.ofLp_toLp, dotProduct, Matrix.mulVec, Pi.star_apply,
    star_star, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem raised_quadratic_eq_dualNormMat
    (H : Herm n) (hH : H.IsHermitian) (hdet : IsUnit H.det) (ξ : ComplexVector n) :
    ellipsoidQuadratic H
        (WithLp.toLp 2 (star (WithLp.ofLp (matrixFiberMap (H⁻¹)ᵀ ξ)))) =
      dualNormMat H ξ := by
  have hK : ((H⁻¹)ᵀ).IsHermitian := hH.inv.transpose
  rw [ellipsoidQuadratic_conjugate, ellipsoidQuadratic_matrixFiberMap, hK.eq]
  have hcancel : Hᵀ * (H⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul H hdet, Matrix.transpose_one]
  rw [Matrix.mul_assoc, hcancel, Matrix.mul_one]
  rfl

end Yau.Proofs.C03Aux.ChernGauge
