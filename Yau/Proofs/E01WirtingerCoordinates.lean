import Yau.Proofs.E01MatrixWirtinger
import Yau.Proofs.V03LeviCalculus
import Yau.LeafProofs.L14

/-! Exact basis expansion of the actual first and mixed Wirtinger directions. -/

noncomputable section
open scoped Matrix

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint
open Yau.Blueprint.V03Proof

variable {n : ℕ}

theorem wirt_direction_coordinates (f : ComplexVector n → ℂ) (z v : ComplexVector n) :
    wirt f z v = ∑ i, v i * wirt f z (stdVec i) := by
  have heq : wirt f z v = star (wirtBar (fun w => star (f w)) z v) := by
    rw [wirtBar_conj, star_star]
  rw [heq, Yau.LeafProofs.L14Aux.wirtBar_direction_coordinates]
  simp only [star_sum, star_mul, star_star, wirtBar_conj, mul_comm]

theorem mixedWirt_direction_coordinates (f : ComplexVector n → ℂ)
    (z v : ComplexVector n) (hf : ContDiffAt ℝ 2 f z) :
    wirt (fun y => wirtBar f y v) z v =
      ∑ k, ∑ l, (v k * star (v l)) *
        wirt (fun y => wirtBar f y (stdVec l)) z (stdVec k) := by
  rw [wirt_direction_coordinates]
  apply Finset.sum_congr rfl
  intro k _
  have heq : (fun y => wirtBar f y v) =
      (fun y => ∑ l, star (v l) * wirtBar f y (stdVec l)) :=
    funext (fun y => Yau.LeafProofs.L14Aux.wirtBar_direction_coordinates f y v)
  rw [heq]
  have hl (l : Fin n) := wirtBar_differentiableAt hf (stdVec l)
  rw [wirt_sum Finset.univ (fun l y => star (v l) * wirtBar f y (stdVec l)) z (stdVec k)
    (fun l _ => (differentiableAt_const (star (v l))).mul (hl l)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have hc : wirt (fun _ : ComplexVector n => star (v l)) z (stdVec k) = 0 := by simp [wirt]
  rw [wirt_mul (f := fun _ => star (v l)) (g := fun y => wirtBar f y (stdVec l))
    (differentiableAt_const (star (v l))) (hl l), hc]
  ring

theorem complexMatrixWirt_direction_coordinates
    (H : ComplexVector n → Herm n) (z a : ComplexVector n) :
    complexMatrixWirt H z a = ∑ k, a k • complexMatrixWirt H z (stdVec k) := by
  ext i j
  simpa only [complexMatrixWirt, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
    wirt_direction_coordinates (fun w => H w i j) z a

theorem complexMatrixWirtBar_direction_coordinates
    (H : ComplexVector n → Herm n) (z a : ComplexVector n) :
    complexMatrixWirtBar H z a = ∑ l, star (a l) • complexMatrixWirtBar H z (stdVec l) := by
  ext i j
  simpa only [complexMatrixWirtBar, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
    Yau.LeafProofs.L14Aux.wirtBar_direction_coordinates (fun w => H w i j) z a

theorem complexMatrixMixed_direction_coordinates
    (H : ComplexVector n → Herm n) (z a : ComplexVector n)
    (hH : ∀ i j, ContDiffAt ℝ 2 (fun w => H w i j) z) :
    complexMatrixWirt (fun w => complexMatrixWirtBar H w a) z a =
      ∑ k, ∑ l, (a k * star (a l)) •
        complexMatrixWirt (fun w => complexMatrixWirtBar H w (stdVec l)) z (stdVec k) := by
  ext i j
  simpa only [complexMatrixWirt, complexMatrixWirtBar, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul] using mixedWirt_direction_coordinates (fun w => H w i j) z a (hH i j)

end Yau.NodeProofs.E01Aux
