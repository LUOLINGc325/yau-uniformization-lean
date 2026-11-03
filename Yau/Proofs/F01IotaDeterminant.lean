import Yau.Proofs.F01TransformedMatrixIdentity

/-! The determinant and logarithm of the actual realification have the
normalization used by the original initial-surface equation. This is derived
from the native real restriction of the same complex linear operator. -/
noncomputable section
open scoped Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem rawReal_det_normSq (H : Matrix (Fin n) (Fin n) ℂ) :
    (G01Aux.rawReal H).det = Complex.normSq H.det := by
  have heq : G01Aux.rawReal H =
      LinearMap.toMatrix (Yau.LeafProofs.L12Aux.realVec_basis n)
        (Yau.LeafProofs.L12Aux.realVec_basis n)
        ((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℂ).toBasis H).restrictScalars ℝ) := by
    ext a b
    exact (Yau.LeafProofs.L12Aux.real_toMatrix_complex_toLin H a b).symm
  rw [heq, LinearMap.det_toMatrix, LinearMap.det_restrictScalars,
    LinearMap.det_toLin, Algebra.norm_complex_apply]

theorem logDetReal_iota_posDef (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    logDetReal (iota H) = Real.log H.det.re := by
  have him : H.det.im = 0 := (Complex.pos_iff.mp hH.det_pos).2.symm
  have heq : Complex.normSq H.det = H.det.re ^ 2 := by
    rw [Complex.normSq_apply, him]
    ring
  unfold logDetReal
  rw [← G01Aux.rawReal_eq_iota H hH.isHermitian, rawReal_det_normSq, heq, Real.log_pow]
  ring

end Yau.NodeProofs.F01Aux
