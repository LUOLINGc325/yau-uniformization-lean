import Yau.Proofs.D02ImmersionBochnerIdentity

/-! Directional matrix derivatives are exact contractions in the fixed
coordinate basis. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.D02Aux
open Yau Yau.LeafProofs.L14Aux

theorem wirtBar_wirt_direction_coordinates {n : ℕ} {U : Set (ComplexVector n)}
    (hU : IsOpen U) (f : ComplexVector n → ℂ) (hf : ContDiffOn ℝ ∞ f U)
    (z v : ComplexVector n) (hz : z ∈ U) :
    wirtBar (fun w => wirt f w v) z v =
      ∑ p, ∑ q, (v p * star (v q)) *
        wirtBar (fun w => wirt f w (stdVec p)) z (stdVec q) := by
  have hWp (p : Fin n) : DifferentiableAt ℝ (fun w => wirt f w (stdVec p)) z :=
    ((wirt_contDiffOn hU f hf (stdVec p)).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hc (c : ℂ) : wirtBar (fun _ : ComplexVector n => c) z v = 0 := by simp [wirtBar]
  have hdC (p : Fin n) : DifferentiableAt ℝ (fun _ : ComplexVector n => v p) z :=
    differentiableAt_const _
  have hfun : (fun w => wirt f w v) = (fun w => ∑ p, v p * wirt f w (stdVec p)) :=
    funext fun w => wirt_direction_coordinates f w v
  rw [hfun, wirtBar_sum_fun Finset.univ (fun p w => v p * wirt f w (stdVec p)) z v
    (fun p _ => (hWp p).const_mul (v p))]
  simp_rw [wirtBar_mul_rule _ _ z v (hdC _) (hWp _), hc, zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro p _
  rw [wirtBar_direction_coordinates, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem directionMatrixWirt_coordinates {n r : ℕ}
    (D : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (z v : ComplexVector n) :
    directionMatrixWirt D z v = ∑ p, v p • directionMatrixWirt D z (stdVec p) := by
  ext a b
  simp only [directionMatrixWirt, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact wirt_direction_coordinates _ z v

theorem directionMatrixWirtBar_coordinates {n r : ℕ}
    (D : ComplexVector n → Matrix (Fin r) (Fin r) ℂ) (z v : ComplexVector n) :
    directionMatrixWirtBar D z v = ∑ q, star (v q) • directionMatrixWirtBar D z (stdVec q) := by
  ext a b
  simp only [directionMatrixWirtBar, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact wirtBar_direction_coordinates _ z v

theorem mixedMatrixWirt_coordinates {n r : ℕ} {U : Set (ComplexVector n)}
    (hU : IsOpen U) (D : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (hD : ∀ a b, ContDiffOn ℝ ∞ (fun w => D w a b) U)
    (z v : ComplexVector n) (hz : z ∈ U) :
    directionMatrixWirtBar (fun w => directionMatrixWirt D w v) z v =
      ∑ p, ∑ q, (v p * star (v q)) •
        directionMatrixWirtBar (fun w => directionMatrixWirt D w (stdVec p)) z (stdVec q) := by
  ext a b
  simp only [directionMatrixWirtBar, directionMatrixWirt, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  exact wirtBar_wirt_direction_coordinates hU _ (hD a b) z v hz

end Yau.NodeProofs.D02Aux
