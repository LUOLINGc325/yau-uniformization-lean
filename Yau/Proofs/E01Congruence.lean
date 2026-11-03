import Yau.Proofs.E01QuadraticFiber

/-! Exact cotangent quadratic and rank-one matrix congruence. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

def matrixFiberMap (S : Herm n) (η : ComplexVector n) : ComplexVector n :=
  WithLp.toLp 2 (S *ᵥ WithLp.ofLp η)

theorem ofLp_matrixFiberMap (S : Herm n) (η : ComplexVector n) :
    WithLp.ofLp (matrixFiberMap S η) = S *ᵥ WithLp.ofLp η := rfl

theorem ellipsoidQuadratic_matrixFiberMap (S A : Herm n) (η : ComplexVector n) :
    ellipsoidQuadratic A (matrixFiberMap S η) = ellipsoidQuadratic (Sᴴ * A * S) η := by
  simp only [ellipsoidQuadratic, ofLp_matrixFiberMap, Matrix.star_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

theorem contactRankOne_matrixFiberMap (S : Herm n) (η : ComplexVector n) :
    contactRankOne (matrixFiberMap S η) = S * contactRankOne η * Sᴴ := by
  simp only [contactRankOne, ofLp_matrixFiberMap, Matrix.star_mulVec,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

theorem matrixFiberMap_comp (S R : Herm n) (η : ComplexVector n) :
    matrixFiberMap S (matrixFiberMap R η) = matrixFiberMap (S * R) η := by
  apply WithLp.ofLp_injective
  simp only [ofLp_matrixFiberMap, Matrix.mulVec_mulVec]

theorem matrixFiberMap_one (η : ComplexVector n) :
    matrixFiberMap (1 : Herm n) η = η := by
  apply WithLp.ofLp_injective
  simp only [ofLp_matrixFiberMap, Matrix.one_mulVec]

end Yau.NodeProofs.E01Aux
