import Yau.Proofs.C05TensorProductDerivativeNorm
import Yau.Proofs.C05InverseEnergyLaplacian
import Yau.LeafProofs.L23TensorTraceNorm

/-! Norms in the actual metric, with explicit contraction and product
bounds used by the inverse-energy error estimate. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {n r s : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def metricTensorNorm (G : Matrix (RIdx n) (RIdx n) ℝ) (A : CovTensor n r) : ℝ :=
  Real.sqrt (covTensorNormSq G A)

theorem metricTensorNorm_nonneg (G : Matrix (RIdx n) (RIdx n) ℝ) (A : CovTensor n r) :
    0 ≤ metricTensorNorm G A := Real.sqrt_nonneg _

theorem covTensorPair_abs_le_norm (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef)
    (A B : CovTensor n r) :
    |covTensorPair G A B| ≤ metricTensorNorm G A * metricTensorNorm G B := by
  have hh := covTensorPair_sq_le G hG A B
  have hA := Real.sq_sqrt (covTensorNormSq_nonneg G hG A)
  have hB := Real.sq_sqrt (covTensorNormSq_nonneg G hG B)
  have hpos : 0 ≤ metricTensorNorm G A * metricTensorNorm G B :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hs : (metricTensorNorm G A * metricTensorNorm G B) ^ 2 =
      covTensorNormSq G A * covTensorNormSq G B := by
    rw [mul_pow]
    exact congrArg₂ (· * ·) hA hB
  apply abs_le.mpr
  constructor <;> nlinarith

theorem metricTensorNorm_concatProduct (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef)
    (A : CovTensor n r) (B : CovTensor n s) :
    metricTensorNorm G (tensorConcatProduct A B) = metricTensorNorm G A * metricTensorNorm G B := by
  unfold metricTensorNorm
  rw [covTensorNormSq_concatProduct, Real.sqrt_mul (covTensorNormSq_nonneg G hG A)]

theorem metricTensorNorm_roughLap_le (k : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    metricTensorNorm (realMetricFn k c z) (roughLap k c A z) ≤
      Real.sqrt (2 * n : ℕ) * metricTensorNorm (realMetricFn k c z)
        (covariantD k c (covariantD k c A) z) := by
  have he : roughLap k c A z = tensorMetricTrace (realMetricFn k c z)⁻¹
      (covariantD k c (covariantD k c A) z) := rfl
  unfold metricTensorNorm
  rw [he]
  apply (Real.sqrt_le_sqrt (covTensorNormSq_metricTrace_le _
    (Yau.LeafProofs.L12Aux.realMetricFn_posDef k c z hz) _)).trans_eq
  rw [Real.sqrt_mul (by positivity)]

theorem metricTensorNorm_covectorSquare (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef)
    (p : CovTensor n 1) : metricTensorNorm G (covectorSquare p) = metricTensorNorm G p ^ 2 := by
  rw [covectorSquare, metricTensorNorm_concatProduct G hG, pow_two]

theorem metricTensorNorm_covariantD_square_le (k : HermitianField M) (c : M.Carrier)
    (p : ComplexVector n → CovTensor n 1) (z : ComplexVector n)
    (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef)
    (hp : ∀ v, DifferentiableAt ℝ (fun w => p w v) z) :
    metricTensorNorm G (covariantD k c (fun w => covectorSquare (p w)) z) ≤
      2 * metricTensorNorm G (covariantD k c p z) * metricTensorNorm G (p z) := by
  have hh := covariantD_concatProduct_norm_le k c p p z G hG hp hp
  change metricTensorNorm G (covariantD k c (fun w => covectorSquare (p w)) z) ≤ _ at hh
  apply hh.trans_eq
  unfold metricTensorNorm
  ring

end Yau.Proofs.C05Aux
