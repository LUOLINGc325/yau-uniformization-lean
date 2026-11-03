import Yau.Proofs.P06RelativeMatrixClips

noncomputable section
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux.Clip
open Yau
variable {n : ℕ}

theorem metricWhiten_trace_pairing (H A B : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    Matrix.trace (metricWhiten H A * metricWhiten H B) = Matrix.trace (H⁻¹ * A * H⁻¹ * B) := by
  let X := (metricRoot H)⁻¹
  calc
    _ = Matrix.trace ((X * A * X) * (X * B) * X) := by
      congr 1
      simp only [metricWhiten, X, mul_assoc]
    _ = Matrix.trace (X * (X * A * X) * (X * B)) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace ((X * X) * A * (X * X) * B) := by congr 1; simp only [mul_assoc]
    _ = _ := by dsimp only [X]; rw [metricRoot_inv_sq H hH]

/-- The relative entry Hilbert pairing is exactly the original inverse-
metric trace pairing, with both inverse metric factors retained. -/
theorem relativeMatrixHS_inner (H A B : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (hA : A.IsHermitian) :
    inner ℝ (relativeMatrixHS H A) (relativeMatrixHS H B) = (Matrix.trace (H⁻¹ * A * H⁻¹ * B)).re := by
  simp only [relativeMatrixHS]
  rw [matrixToHS_inner _ _ (metricWhiten_hermitian H A hA), metricWhiten_trace_pairing H A B hH]

def pointFormHS {M : ComplexManifold n} (g : HermitianField M) (A : RealForm M 2) (x : M.Carrier) :=
  relativeMatrixHS (gMat g x) (formHermitianMatrix A x)

/-- The computed form inner product has exactly the relative Hilbert–
Schmidt normalization; no dimension or Wirtinger factor is absorbed. -/
theorem formInner_eq_pointFormHS {M : ComplexManifold n} (g : HermitianField M)
    (A B : RealForm M 2) (hA : RealOneOne A) (hB : RealOneOne B) (x : M.Carrier) :
    formInner g A B x = inner ℝ (pointFormHS g A x) (pointFormHS g B x) := by
  rw [Yau.NodeProofs.G04Aux.formInner_oneOne g A B hA hB x]
  exact (relativeMatrixHS_inner _ _ _
    (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))
    ((Yau.NodeProofs.G04Aux.representsSelf A hA).2 x)).symm

theorem formNormSq_eq_pointFormHS {M : ComplexManifold n} (g : HermitianField M)
    (A : RealForm M 2) (hA : RealOneOne A) (x : M.Carrier) :
    formNormSq g A x = ‖pointFormHS g A x‖ ^ 2 := by
  rw [formNormSq, formInner_eq_pointFormHS g A A hA hA x, real_inner_self_eq_norm_sq]

end Yau.NodeProofs.P06Aux.Clip
