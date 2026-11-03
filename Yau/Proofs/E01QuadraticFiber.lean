import Yau.Proofs.E01Matrix

/-! Continuity and exact complex homogeneity of the original fiber quadratic form. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem continuous_ellipsoidQuadratic_joint :
    Continuous (fun p : Herm n × ComplexVector n => ellipsoidQuadratic p.1 p.2) := by
  unfold ellipsoidQuadratic Matrix.mulVec dotProduct
  fun_prop

theorem continuous_ellipsoidQuadratic_fiber (A : Herm n) :
    Continuous (ellipsoidQuadratic A) :=
  continuous_ellipsoidQuadratic_joint.comp (continuous_const.prodMk continuous_id)

theorem ellipsoidQuadratic_complex_smul (A : Herm n) (c : ℂ) (η : ComplexVector n) :
    ellipsoidQuadratic A (c • η) = ‖c‖ ^ 2 * ellipsoidQuadratic A η := by
  have hc : WithLp.ofLp (c • η) = c • WithLp.ofLp η := rfl
  unfold ellipsoidQuadratic
  rw [hc, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem ellipsoidQuadratic_real_vector_smul (A : Herm n) (r : ℝ)
    (η : ComplexVector n) :
    ellipsoidQuadratic A ((r : ℂ) • η) = r ^ 2 * ellipsoidQuadratic A η := by
  rw [ellipsoidQuadratic_complex_smul]
  simp [Complex.norm_real, Real.norm_eq_abs]

end Yau.NodeProofs.E01Aux
