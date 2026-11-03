import Yau.Proofs.G01Realification
import Yau.LeafProofs.L05ComplexRepresentation

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G04Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem rawReal_det (H : Matrix (Fin n) (Fin n) ℂ) :
    (G01Aux.rawReal H).det = Complex.normSq H.det := by
  have ht : G01Aux.rawReal H = LinearMap.toMatrix (L12Aux.realVec_basis n)
      (L12Aux.realVec_basis n)
      ((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis H).restrictScalars ℝ) := by
    ext a b
    exact (L12Aux.real_toMatrix_complex_toLin H a b).symm
  rw [ht, LinearMap.det_toMatrix, LinearMap.det_restrictScalars,
    LinearMap.det_toLin, Algebra.norm_complex_apply]

theorem rawReal_inv (H : Matrix (Fin n) (Fin n) ℂ) (hH : IsUnit H.det) :
    (G01Aux.rawReal H)⁻¹ = G01Aux.rawReal H⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← G01Aux.rawReal_mul, Matrix.mul_nonsing_inv _ hH, G01Aux.rawReal_one]

theorem parabolicLogDet (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    Parabolic.logDetReal (Parabolic.iota H) = Real.log H.det.re := by
  unfold Parabolic.logDetReal
  rw [← G01Aux.rawReal_eq_iota H hH.1, rawReal_det]
  have him : H.det.im = 0 := (Complex.pos_iff.mp hH.det_pos).2.symm
  rw [Complex.normSq_apply, him, mul_zero, add_zero, ← pow_two, Real.log_pow]
  ring

theorem parabolicTrace (H A : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (hA : A.IsHermitian) :
    Matrix.trace ((Parabolic.iota H : Parabolic.Mat n)⁻¹ *
      (Parabolic.iota A : Parabolic.Mat n)) = 2 * traceWith H A := by
  rw [← G01Aux.rawReal_eq_iota H hH.1, ← G01Aux.rawReal_eq_iota A hA,
    rawReal_inv H (hH.isUnit.map Matrix.detMonoidHom),
    ← G01Aux.rawReal_mul, G01Aux.rawReal_trace]
  rfl

theorem complexHessianNormalization : ComplexHessianRepresentation :=
  L05Aux.complexHessianRepresentation

theorem parabolicNormalization : PaperParabolicMatrixNormalizationTarget := by
  refine ⟨complexHessianNormalization, ?_⟩
  intro n H hH
  exact ⟨parabolicLogDet H hH, fun A hA => parabolicTrace H A hH hA⟩

end Yau.NodeProofs.G04Aux
