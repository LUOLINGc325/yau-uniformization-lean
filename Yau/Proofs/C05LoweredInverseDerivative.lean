import Yau.Proofs.C05LoweredInverse
import Yau.LeafProofs.L23TensorSlots

/-! The genuine covariant derivative of a lowered inverse form. No
coordinate frame is varied with the flow. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def matrixCovTensor (B : Matrix (RIdx n) (RIdx n) ℝ) : CovTensor n 2 :=
  fun v => B (v 0) (v 1)

def matrixCovariantD (k : HermitianField M) (c : M.Carrier)
    (B : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (z : ComplexVector n) (i : RIdx n) : Matrix (RIdx n) (RIdx n) ℝ :=
  matrixDirectionalDerivative B z (realVec i) -
    (connectionMatrix k c z i)ᵀ * B z - B z * connectionMatrix k c z i

theorem covariantD_matrixCovTensor (k : HermitianField M) (c : M.Carrier)
    (B : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (z : ComplexVector n) (i a b : RIdx n) :
    covariantD k c (fun w => matrixCovTensor (B w)) z ![i, a, b] =
      matrixCovariantD k c B z i a b := by
  simp [covariantD, matrixCovTensor, matrixCovariantD, matrixDirectionalDerivative,
    Fin.sum_univ_succ, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    connectionMatrix, rDeriv, mul_comm, sub_sub]

theorem matrixDirectionalDerivative_loweredInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G A : E → Matrix (RIdx n) (RIdx n) ℝ) (z v : E)
    (hG : ∀ a b, DifferentiableAt ℝ (fun w => G w a b) z)
    (hA : ∀ a b, DifferentiableAt ℝ (fun w => A w a b) z)
    (hdet : (A z).det ≠ 0) :
    matrixDirectionalDerivative (fun w => loweredInverseMatrix (G w) (A w)) z v =
      matrixDirectionalDerivative G z v * (A z)⁻¹ * G z +
        G z * (-((A z)⁻¹ * matrixDirectionalDerivative A z v * (A z)⁻¹)) * G z +
          G z * (A z)⁻¹ * matrixDirectionalDerivative G z v := by
  have hI := matrixInverse_entries_differentiableAt hA hdet
  unfold loweredInverseMatrix
  rw [matrixDirectionalDerivative_mul (matrix_entries_differentiable_mul hG hI) hG v,
    matrixDirectionalDerivative_mul hG hI v, matrixDirectionalDerivative_inv hA hdet v]
  noncomm_ring

theorem matrixCovariantD_loweredInverse (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hA : ∀ a b, DifferentiableAt ℝ (fun w => A w a b) z)
    (hdet : (A z).det ≠ 0) (i : RIdx n) :
    matrixCovariantD k c (fun w => loweredInverseMatrix (realMetricFn k c w) (A w)) z i =
      -(realMetricFn k c z * (A z)⁻¹ * matrixCovariantD k c A z i *
        (A z)⁻¹ * realMetricFn k c z) := by
  have hG (a b : RIdx n) := ((hk c a b).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  let D := connectionMatrix k c z i
  have hDA : matrixDirectionalDerivative A z (realVec i) =
      matrixCovariantD k c A z i + Dᵀ * A z + A z * D := by
    unfold matrixCovariantD
    dsimp only [D]
    abel
  change matrixDirectionalDerivative
      (fun w => loweredInverseMatrix (realMetricFn k c w) (A w)) z (realVec i) -
    Dᵀ * loweredInverseMatrix (realMetricFn k c z) (A z) -
      loweredInverseMatrix (realMetricFn k c z) (A z) * D = _
  rw [matrixDirectionalDerivative_loweredInverse _ _ z _ hG hA hdet,
    Yau.LeafProofs.L23Aux.metricDirectionalDerivative_eq_connection k hk c z hz i, hDA]
  exact loweredInverseMatrix_covariant_algebra (realMetricFn k c z) (A z) D
    (matrixCovariantD k c A z i) hdet

end Yau.Proofs.C05Aux
