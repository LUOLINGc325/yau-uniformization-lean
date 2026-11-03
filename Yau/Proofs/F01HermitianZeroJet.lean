import Yau.Proofs.F01WirtingerLinear
import Yau.LeafProofs.L14

/-! For an actual Hermitian matrix family, vanishing holomorphic first
coordinate jets also kills the barred jets and the complete real derivative. -/
noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem hermitian_matrix_real_first_jet_zero
    (G : ComplexVector n → Matrix (Fin n) (Fin n) ℂ) (z : ComplexVector n)
    (hG : ∀ w, (G w).IsHermitian)
    (hzero : ∀ i j k, wirt (fun w => G w i j) z (stdVec k) = 0) (i j : Fin n) :
    fderiv ℝ (fun w => G w i j) z = 0 := by
  have hwzero (p q : Fin n) (v : ComplexVector n) : wirt (fun w => G w p q) z v = 0 := by
    rw [wirt_eq_coordinate_contraction]
    simp only [hzero, dotProduct, zero_mul, Finset.sum_const_zero]
  have hfun : (fun w => G w i j) = (fun w => star (G w j i)) := by
    funext w
    exact (hG w).apply i j |>.symm
  have hbzero (v : ComplexVector n) : wirtBar (fun w => G w i j) z v = 0 := by
    rw [hfun, L14Aux.wirtBar_star, hwzero, star_zero]
  ext v
  have hsplit : fderiv ℝ (fun w => G w i j) z v =
      wirt (fun w => G w i j) z v + wirtBar (fun w => G w i j) z v := by
    unfold wirt wirtBar
    ring
  rw [hsplit, hwzero, hbzero]
  simp

end Yau.NodeProofs.F01Aux
