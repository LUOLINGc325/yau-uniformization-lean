import Yau.Proofs.V04WallErrorContractionFinal
import Yau.Proofs.V04WallErrorInverseHessian
import Yau.Proofs.V04WallErrorKahler

/-! The finite contraction applied to the actual smooth Kähler metric. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof Yau.NodeProofs.G01Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem kahler_contracted_inverse_hessian
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (l k : Fin n) :
    (∑ i, ∑ j, (hMat h x z)⁻¹ j i *
      mixedMatrixWirt (fun w => (hMat h x w)⁻¹) z i j l k) -
    (∑ i, ∑ j, matrixWirtBar (fun w => (hMat h x w)⁻¹) z i j k *
      matrixWirt (fun w => (hMat h x w)⁻¹) z j l i) =
    ((hMat h x z)⁻¹ * (-leviC (logDet h x) z) * (hMat h x z)⁻¹) l k := by
  let H := hMat h x
  have hOp := isOpen_extChartAt_target (I := ComplexModel n) x
  have hH := Yau.LeafProofs.L17Aux.hMat_contDiffOn_of_metricSmooth h hs x
  have hdet : ∀ w ∈ chartTarget x, (H w).det ≠ 0 :=
    fun w hw => (hMat_posDef h x w hw).det_pos.ne'
  have hD : ∀ j p q, matrixWirt H z j p q = matrixWirt H z q p j :=
    fun j p q => kahler_hMat_wirt_symm h hs hk x z hz j q p
  have hB : ∀ i p q, matrixWirtBar H z i p q = matrixWirtBar H z p i q :=
    fun i p q => kahler_hMat_wirtBar_symm h hs hk x z hz i p q
  have hS : ∀ i j p q, mixedMatrixWirt H z i j p q = mixedMatrixWirt H z p q i j :=
    fun i j p q => kahler_hMat_mixed_pair_symmetry h hs hk x hz i j p q
  have hR : Matrix.of (fun p s =>
      Matrix.trace ((H z)⁻¹ * matrixWirt H z s * (H z)⁻¹ * matrixWirtBar H z p) -
        Matrix.trace ((H z)⁻¹ * mixedMatrixWirt H z p s)) = -leviC (logDet h x) z := by
    ext p s
    exact (ricci_entry_jacobi hOp hH (fun w hw => hMat_posDef h x w hw) hz p s).symm
  have hc := contracted_inverse_hessian_identity (H z)⁻¹ (matrixWirt H z)
    (matrixWirtBar H z) (mixedMatrixWirt H z) hD hB hS l k
  rw [hR] at hc
  simp_rw [mixedMatrixWirt_inverse hOp hH hdet hz,
    matrixWirtBar_inverse hOp hH hdet hz, matrixWirt_inverse hOp hH hdet hz]
  exact hc

theorem matrixWirtBar_inverse_star (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (j i b : Fin n) :
    star (matrixWirtBar (fun w => (hMat h x w)⁻¹) z j i b) =
      matrixWirt (fun w => (hMat h x w)⁻¹) z j b i := by
  have he : (fun w => star ((hMat h x w)⁻¹ i b)) =
      (fun w => (hMat h x w)⁻¹ b i) := by
    funext w
    exact ((hMat_isHermitian h x w).inv).apply b i
  change star (wirtBar (fun w => (hMat h x w)⁻¹ i b) z (stdVec j)) = _
  rw [← wirt_conj, he]
  rfl

end Yau.Blueprint.V04Proof.WallErrorAux
