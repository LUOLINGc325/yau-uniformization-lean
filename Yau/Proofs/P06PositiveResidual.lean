import Yau.Proofs.P06HodgeClipping
import Yau.Proofs.P06HodgeTypeResolvent

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux.Clip
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem metricWhiten_neg (H A : Matrix (Fin n) (Fin n) ℂ) : metricWhiten H (-A) = -metricWhiten H A := by
  simp only [metricWhiten, mul_neg, neg_mul]

theorem formHermitianMatrix_neg (A : RealForm M 2) (x : M.Carrier) :
    formHermitianMatrix (-A) x = -formHermitianMatrix A x := by
  rw [← neg_one_smul ℝ A, G04Aux.formHermitianMatrix_real_smul]
  simp

theorem realOneOne_neg (A : RealForm M 2) (hA : RealOneOne A) : RealOneOne (-A) := by
  simpa only [zero_sub] using realOneOne_sub 0 A (by intro x u v; rfl) hA

theorem relativePositivePart_split (H A : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (hA : A.IsHermitian) :
    A = relativePositivePart H A - relativePositivePart H (-A) := by
  have hs : IsSelfAdjoint (metricWhiten H A) := metricWhiten_hermitian H A hA
  have he : metricWhiten H A = matrixPositivePart (metricWhiten H A) -
      matrixPositivePart (-metricWhiten H A) := by
    simp only [matrixPositivePart, CFC.posPart_neg]
    exact (CFC.posPart_sub_negPart _ hs).symm
  calc
    _ = metricUnwhiten H (metricWhiten H A) := (metricUnwhiten_whiten H A hH).symm
    _ = _ := by
      rw [he, metricUnwhiten_sub]
      simp only [relativePositivePart, metricWhiten_neg]

theorem positiveForm_split (g : HermitianField M) (A : RealForm M 2) (hA : RealOneOne A) :
    A = positiveForm g A - positiveForm g (-A) := by
  funext x
  apply oneOne_eq_at_of_matrix_eq g _ _ hA
    (realOneOne_sub _ _ (positiveForm_oneOne g A) (positiveForm_oneOne g (-A))) x
  rw [formHermitianMatrix_sub, positiveForm_matrix, positiveForm_matrix, formHermitianMatrix_neg]
  exact relativePositivePart_split _ _
    (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))
    ((G04Aux.representsSelf A hA).2 x)

theorem pointFormHS_positive (g : HermitianField M) (A : RealForm M 2) (x : M.Carrier) :
    pointFormHS g (positiveForm g A) x = matrixToHS
      (matrixPositivePart (metricWhiten (gMat g x) (formHermitianMatrix A x))) := by
  rw [pointFormHS, positiveForm_matrix, relativeMatrixHS, metricWhiten_relativePositivePart]
  exact Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)

theorem formInner_positive_neg_zero (g : HermitianField M) (A : RealForm M 2) (x : M.Carrier) :
    formInner g (positiveForm g A) (positiveForm g (-A)) x = 0 := by
  rw [formInner_eq_pointFormHS g _ _ (positiveForm_oneOne g A) (positiveForm_oneOne g (-A)) x,
    pointFormHS_positive, pointFormHS_positive, formHermitianMatrix_neg, metricWhiten_neg,
    matrixToHS_inner _ _ (matrixPositivePart_posSemidef _).1]
  simp only [matrixPositivePart, CFC.posPart_neg, CFC.posPart_mul_negPart,
    Matrix.trace_zero, Complex.zero_re]

theorem positiveForm_residual (g : HermitianField M) (A : RealForm M 2) (hA : RealOneOne A) :
    A - positiveForm g A = -positiveForm g (-A) := by
  calc
    _ = (positiveForm g A - positiveForm g (-A)) - positiveForm g A :=
      congrArg (fun B : RealForm M 2 => B - positiveForm g A) (positiveForm_split g A hA)
    _ = _ := by abel

end Yau.NodeProofs.P06Aux.Clip
