import Yau.Proofs.C02UnitaryMatrixTrace
import Yau.Proofs.C02Frames
import Yau.LeafProofs.L12

noncomputable section
open scoped Matrix Manifold InnerProductSpace
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def unitaryFrameMatrix (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p) : Matrix (Fin n) (Fin n) ℂ :=
  fun a i => tangentCoords p p (U (stdVec i)) a

theorem tangentVector_coordinate_sum (p : M.Carrier) (v : TangentVector M p) :
    (∑ a, tangentCoords p p v a • chartVec p p (stdVec a)) = v := by
  let L : ComplexVector n →L[ℂ] TangentVector M p :=
    mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) p).symm (chartPt p p)
  calc
    _ = ∑ a, L (tangentCoords p p v a • stdVec a) :=
      Finset.sum_congr rfl (fun a _ => (L.map_smul _ _).symm)
    _ = L (∑ a, tangentCoords p p v a • stdVec a) := (map_sum L _ _).symm
    _ = L (tangentCoords p p v) := congrArg L (complexVector_basis_sum _)
    _ = v := by
      change chartVec p p (tangentCoords p p v) = v
      exact chartVec_tangentCoords p p (mem_extChartAt_source p) v

theorem unitaryFrameMatrix_gram (h : HermitianField M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (h p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    (unitaryFrameMatrix p U).conjTranspose * gMat h p * unitaryFrameMatrix p U = 1 := by
  ext i j
  have hFrame := hU (stdVec i) (stdVec j)
  rw [← tangentVector_coordinate_sum p (U (stdVec i)),
    ← tangentVector_coordinate_sum p (U (stdVec j)), hermitian_sum_left] at hFrame
  simp only [hermitian_sum_right, HermitianInnerProduct.map_smul_left,
    HermitianInnerProduct.map_smul_right] at hFrame
  have hp : chartInv p (chartPt p p) = p := (extChartAt (ComplexModel n) p).left_inv (mem_extChartAt_source p)
  have hG (a b : Fin n) : gMat h p a b =
      (h p).toFun (chartVec p p (stdVec a)) (chartVec p p (stdVec b)) := by
    unfold gMat hMat
    rw [hp]
  change (_ : Matrix (Fin n) (Fin n) ℂ) i j = if i = j then 1 else 0
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, unitaryFrameMatrix,
    Finset.mul_sum]
  simp_rw [hG, ← mul_assoc]
  rw [hFrame]
  simp [stdVec, EuclideanSpace.inner_single_left, eq_comm]

end Yau.Blueprint.C02Proof
