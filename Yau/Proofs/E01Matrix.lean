import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! The quadratic and rank-one conventions in the original ellipsoid contract. -/

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

def ellipsoidQuadratic (D : Herm n) (η : ComplexVector n) : ℝ :=
  (star (WithLp.ofLp η) ⬝ᵥ (D *ᵥ WithLp.ofLp η)).re

def contactRankOne (η : ComplexVector n) : Herm n :=
  Matrix.vecMulVec (WithLp.ofLp η) (star (WithLp.ofLp η))

theorem ellipsoidQuadratic_zero (η : ComplexVector n) :
    ellipsoidQuadratic (0 : Herm n) η = 0 := by
  simp [ellipsoidQuadratic]

theorem ellipsoidQuadratic_zero_vector (D : Herm n) :
    ellipsoidQuadratic D 0 = 0 := by
  simp [ellipsoidQuadratic]

theorem ellipsoidQuadratic_add (A B : Herm n) (η : ComplexVector n) :
    ellipsoidQuadratic (A + B) η =
      ellipsoidQuadratic A η + ellipsoidQuadratic B η := by
  simp [ellipsoidQuadratic, Matrix.add_mulVec, dotProduct_add]

theorem ellipsoidQuadratic_real_smul (r : ℝ) (A : Herm n) (η : ComplexVector n) :
    ellipsoidQuadratic ((r : ℂ) • A) η = r * ellipsoidQuadratic A η := by
  simp [ellipsoidQuadratic, Matrix.smul_mulVec, dotProduct_smul,
    Complex.mul_re]

theorem ellipsoidQuadratic_nonneg {A : Herm n} (hA : A.PosSemidef)
    (η : ComplexVector n) : 0 ≤ ellipsoidQuadratic A η :=
  (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg (WithLp.ofLp η))).1

theorem ellipsoidQuadratic_pos {A : Herm n} (hA : A.PosDef)
    {η : ComplexVector n} (hη : η ≠ 0) : 0 < ellipsoidQuadratic A η := by
  apply (Complex.pos_iff.mp (hA.dotProduct_mulVec_pos ?_)).1
  intro hzero
  apply hη
  ext i
  exact congrArg (fun u : Fin n → ℂ => u i) hzero

theorem contactRankOne_posSemidef (η : ComplexVector n) :
    (contactRankOne η).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (WithLp.ofLp η)

theorem contactRankOne_trace (η : ComplexVector n) :
    (Matrix.trace (contactRankOne η)).re = ‖η‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ i, η i * star (η i)).re = ∑ i, ‖η i‖ ^ 2
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

theorem trace_mul_contactRankOne (A : Herm n) (η : ComplexVector n) :
    (Matrix.trace (A * contactRankOne η)).re = ellipsoidQuadratic A η := by
  simp only [contactRankOne, ellipsoidQuadratic, Matrix.mul_vecMulVec,
    Matrix.trace_vecMulVec, dotProduct_comm]

theorem ellipsoidQuadratic_one (η : ComplexVector n) :
    ellipsoidQuadratic (1 : Herm n) η = ‖η‖ ^ 2 := by
  rw [← trace_mul_contactRankOne, Matrix.one_mul, contactRankOne_trace]

end Yau.NodeProofs.E01Aux
