import Yau.Proofs.E01LeviAlgebra
import Yau.Proofs.E01DualScale

/-! Finite-dimensional inverse quadratic estimates and actual pullback cancellation. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.Proofs.C03Aux.QOne
open Yau Yau.Blueprint Yau.NodeProofs.E01Aux
variable {n : ℕ}

theorem inverse_congruence_cancel (J H : Herm n) (hJ : IsUnit J.det) :
    J * (Jᴴ * H * J)⁻¹ * Jᴴ = H⁻¹ := by
  have hJH : IsUnit Jᴴ.det := by simpa only [Matrix.det_conjTranspose] using hJ.star
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv J hJ, Matrix.one_mul]
  exact Matrix.nonsing_inv_mul_cancel_right Jᴴ H⁻¹ hJH

theorem quadratic_pullback_cancel (J H : Herm n) (hJ : IsUnit J.det)
    (s : ℂ) (F : ComplexVector n) :
    ellipsoidQuadratic (Jᴴ * H * J)⁻¹ (s • matrixFiberMap Jᴴ F) =
      ‖s‖ ^ 2 * ellipsoidQuadratic H⁻¹ F := by
  rw [ellipsoidQuadratic_complex_smul, ellipsoidQuadratic_matrixFiberMap,
    Matrix.conjTranspose_conjTranspose, inverse_congruence_cancel J H hJ]

theorem dualNormMat_pullback_cancel (J H : Herm n) (hJ : IsUnit J.det)
    (α : ComplexVector n) :
    dualNormMat (Jᴴ * H * J) (matrixFiberMap Jᵀ α) = dualNormMat H α := by
  change ellipsoidQuadratic ((Jᴴ * H * J)⁻¹)ᵀ (matrixFiberMap Jᵀ α) =
    ellipsoidQuadratic (H⁻¹)ᵀ α
  rw [ellipsoidQuadratic_matrixFiberMap]
  congr 1
  have ht := congrArg Matrix.transpose (inverse_congruence_cancel J H hJ)
  have hc : (Jᵀ)ᴴ = (Jᴴ)ᵀ := rfl
  simpa only [Matrix.transpose_mul, Matrix.mul_assoc, hc] using ht

theorem quadratic_inverse_image (H : Herm n) (hH : H.PosDef) (F : ComplexVector n) :
    ellipsoidQuadratic H (matrixFiberMap H⁻¹ F) = ellipsoidQuadratic H⁻¹ F := by
  rw [ellipsoidQuadratic_matrixFiberMap, hH.inv.1.eq]
  have hu : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv H hu, Matrix.mul_one]

theorem inverse_quadratic_young (H : Herm n) (hH : H.PosDef)
    (τ : ℝ) (hτ : 0 < τ) (F V : ComplexVector n) :
    2 * (star (WithLp.ofLp F) ⬝ᵥ WithLp.ofLp V).re -
        τ * ellipsoidQuadratic H V ≤ ellipsoidQuadratic H⁻¹ F / τ := by
  have hu : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  let W := ((τ⁻¹ : ℝ) : ℂ) • matrixFiberMap H⁻¹ F
  have he : H *ᵥ WithLp.ofLp W = ((τ⁻¹ : ℝ) : ℂ) • WithLp.ofLp F := by
    change H *ᵥ (((τ⁻¹ : ℝ) : ℂ) • (H⁻¹ *ᵥ WithLp.ofLp F)) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H hu,
      Matrix.one_mulVec]
  have hq : ellipsoidQuadratic H W = τ⁻¹ ^ 2 * ellipsoidQuadratic H⁻¹ F := by
    exact (ellipsoidQuadratic_real_vector_smul H τ⁻¹ (matrixFiberMap H⁻¹ F)).trans
      (congrArg (fun t : ℝ => τ⁻¹ ^ 2 * t) (quadratic_inverse_image H hH F))
  have hp : (star (WithLp.ofLp V) ⬝ᵥ (H *ᵥ WithLp.ofLp W)).re =
      τ⁻¹ * (star (WithLp.ofLp F) ⬝ᵥ WithLp.ofLp V).re := by
    rw [he, dotProduct_smul]
    have hc : (star (WithLp.ofLp V) ⬝ᵥ WithLp.ofLp F).re =
        (star (WithLp.ofLp F) ⬝ᵥ WithLp.ofLp V).re := by
      simpa only [Matrix.one_mulVec] using
        hermitian_pairing_re_comm (1 : Herm n) (by simp) V F
    simpa only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hc]
  have hn := ellipsoidQuadratic_nonneg hH.posSemidef (V - W)
  rw [ellipsoidQuadratic_vector_sub H hH.1, hq, hp] at hn
  have ht := mul_nonneg hτ.le hn
  field_simp at ht ⊢
  nlinarith

end Yau.Proofs.C03Aux.QOne
