import Yau.Proofs.V04WallErrorRicci
import Yau.Proofs.V03ClearedWalls

/-! The mixed second derivative of the actual inverse matrix. Every
identity is differentiated on the open set of invertibility. -/

open Filter
open scoped Manifold Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof Yau.NodeProofs.G01Aux

variable {n r : ℕ}

theorem matrixWirt_congr_of_eventuallyEq
    {A B : ComplexVector n → Matrix (Fin r) (Fin r) ℂ} {z : ComplexVector n}
    (heq : A =ᶠ[𝓝 z] B) (k : Fin n) : matrixWirt A z k = matrixWirt B z k := by
  ext a b
  have heq' : (fun w => A w a b) =ᶠ[𝓝 z] (fun w => B w a b) :=
    heq.mono fun _ h => congrArg (fun C : Matrix (Fin r) (Fin r) ℂ => C a b) h
  simp only [matrixWirt, wirt, heq'.fderiv_eq (𝕜 := ℝ)]

theorem matrixWirt_neg (A : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (k : Fin n) : matrixWirt (fun w => -A w) z k = -matrixWirt A z k := by
  ext a b
  exact wirt_neg (fun w => A w a b) z (stdVec k)

theorem mixedMatrixWirt_inverse
    {H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ} {U : Set (ComplexVector n)}
    (hU : IsOpen U) (hH : ∀ a b, ContDiffOn ℝ ∞ (fun z => H z a b) U)
    (hdet : ∀ z ∈ U, (H z).det ≠ 0) {z : ComplexVector n} (hz : z ∈ U) (i j : Fin n) :
    mixedMatrixWirt (fun w => (H w)⁻¹) z i j =
      (H z)⁻¹ * matrixWirt H z j * (H z)⁻¹ * matrixWirtBar H z i * (H z)⁻¹ +
      (H z)⁻¹ * matrixWirtBar H z i * (H z)⁻¹ * matrixWirt H z j * (H z)⁻¹ -
      (H z)⁻¹ * mixedMatrixWirt H z i j * (H z)⁻¹ := by
  have hInv (a b : Fin r) : ContDiffOn ℝ ∞ (fun w => (H w)⁻¹ a b) U :=
    entrywise_matrix_inv_contDiffOn hH hdet a b
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
  have heq : (fun w => matrixWirtBar (fun u => (H u)⁻¹) w i) =ᶠ[𝓝 z]
      (fun w => -((H w)⁻¹ * matrixWirtBar H w i * (H w)⁻¹)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    simpa only [Matrix.neg_mul] using matrixWirtBar_inverse hU hH hdet hw i
  change matrixWirt (fun w => matrixWirtBar (fun u => (H u)⁻¹) w i) z j = _
  rw [matrixWirt_congr_of_eventuallyEq heq j, matrixWirt_neg,
    matrixWirt_mul (fun w => (H w)⁻¹ * matrixWirtBar H w i)
      (fun w => (H w)⁻¹) z hPD hID j,
    matrixWirt_mul (fun w => (H w)⁻¹) (fun w => matrixWirtBar H w i) z hID hBD j,
    matrixWirt_inverse hU hH hdet hz j]
  unfold mixedMatrixWirt
  noncomm_ring

end Yau.Blueprint.V04Proof.WallErrorAux
