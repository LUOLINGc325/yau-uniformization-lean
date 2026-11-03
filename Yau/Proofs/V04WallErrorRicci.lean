import Yau.Proofs.V04WallErrorJacobi
import Yau.Proofs.V03ClearedWalls

/-! The Ricci calculator expressed by the same first and mixed matrix
derivatives used in the inverse-metric Hessian. -/

open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof Yau.NodeProofs.G01Aux

variable {n r : ℕ}

def mixedMatrixWirt (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (i j : Fin n) : Matrix (Fin r) (Fin r) ℂ :=
  matrixWirt (fun w => matrixWirtBar H w i) z j

theorem matrixWirt_trace {A : ComplexVector n → Matrix (Fin r) (Fin r) ℂ}
    {z : ComplexVector n} (hA : ∀ a b, DifferentiableAt ℝ (fun w => A w a b) z)
    (k : Fin n) :
    wirt (fun w => Matrix.trace (A w)) z (stdVec k) = Matrix.trace (matrixWirt A z k) := by
  change wirt (fun w => ∑ i, A w i i) z (stdVec k) = _
  rw [wirt_sum Finset.univ (fun i w => A w i i) z (stdVec k) (fun i _ => hA i i)]
  rfl

theorem ricci_entry_jacobi
    {H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ} {U : Set (ComplexVector n)}
    (hU : IsOpen U) (hH : ∀ a b, ContDiffOn ℝ ∞ (fun z => H z a b) U)
    (hpos : ∀ z ∈ U, (H z).PosDef) {z : ComplexVector n} (hz : z ∈ U) (i j : Fin n) :
    (-leviC (fun w => Real.log (H w).det.re) z) i j =
      Matrix.trace ((H z)⁻¹ * matrixWirt H z j * (H z)⁻¹ * matrixWirtBar H z i) -
        Matrix.trace ((H z)⁻¹ * mixedMatrixWirt H z i j) := by
  have hInv (a b : Fin r) : ContDiffOn ℝ ∞ (fun w => (H w)⁻¹ a b) U :=
    entrywise_matrix_inv_contDiffOn hH (fun w hw => (hpos w hw).det_pos.ne') a b
  have hBar (a b : Fin r) : ContDiffOn ℝ ∞ (fun w => matrixWirtBar H w i a b) U :=
    wirtBar_contDiffOn hU (hH a b) (stdVec i)
  have hID (a b : Fin r) : DifferentiableAt ℝ (fun w => (H w)⁻¹ a b) z :=
    ((hInv a b).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hBD (a b : Fin r) : DifferentiableAt ℝ (fun w => matrixWirtBar H w i a b) z :=
    ((hBar a b).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hPD (a b : Fin r) : DifferentiableAt ℝ
      (fun w => ((H w)⁻¹ * matrixWirtBar H w i) a b) z := by
    change DifferentiableAt ℝ (fun w => ∑ c, (H w)⁻¹ a c * matrixWirtBar H w i c b) z
    exact DifferentiableAt.fun_sum (fun c _ => (hID a c).mul (hBD c b))
  have heq : (fun w => wirtBar (fun u => (Real.log (H u).det.re : ℂ)) w (stdVec i)) =ᶠ[𝓝 z]
      (fun w => Matrix.trace ((H w)⁻¹ * matrixWirtBar H w i)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact matrix_jacobi_wirtBar_logdet hU hH hpos hw i
  change -wirt (fun w => wirtBar (fun u => (Real.log (H u).det.re : ℂ)) w (stdVec i))
    z (stdVec j) = _
  have hw : wirt (fun w => wirtBar (fun u => (Real.log (H u).det.re : ℂ)) w (stdVec i))
      z (stdVec j) = wirt (fun w => Matrix.trace ((H w)⁻¹ * matrixWirtBar H w i)) z (stdVec j) := by
    simp only [wirt, heq.fderiv_eq (𝕜 := ℝ)]
  rw [hw, matrixWirt_trace hPD j,
    matrixWirt_mul (fun w => (H w)⁻¹) (fun w => matrixWirtBar H w i) z hID hBD j,
    matrixWirt_inverse hU hH (fun w hw => (hpos w hw).det_pos.ne') hz j]
  simp only [mixedMatrixWirt, Matrix.neg_mul, Matrix.trace_add, Matrix.trace_neg]
  ring

end Yau.Blueprint.V04Proof.WallErrorAux
