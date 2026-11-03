import Yau.Proofs.C02RealUnitaryMatrix
import Yau.LeafProofs.L23TensorCalculus

noncomputable section
open scoped Matrix
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L23Aux
variable {n r : ℕ}

theorem sqrt_covTensorNormSq_eq_frame_norm
    (G D : Matrix (RIdx n) (RIdx n) ℝ) (hD : D.transpose * G * D = 1)
    (A : CovTensor n r) :
    Real.sqrt (covTensorNormSq G A) =
      ‖(WithLp.toLp 2 (tensorFrameTransform D A) : EuclideanSpace ℝ (Fin r → RIdx n))‖ := by
  have heq : covTensorNormSq G A =
      ‖(WithLp.toLp 2 (tensorFrameTransform D A) : EuclideanSpace ℝ (Fin r → RIdx n))‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    unfold covTensorNormSq
    rw [tensor_contraction_eq_frame_sum G⁻¹ D (inverseMetric_of_orthonormalMatrix G D hD)]
    simp only [pow_two, WithLp.ofLp_toLp]
  rw [heq, Real.sqrt_sq (norm_nonneg _)]

end Yau.Blueprint.C02Proof
