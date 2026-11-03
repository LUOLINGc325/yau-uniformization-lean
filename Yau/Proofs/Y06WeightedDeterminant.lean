import Yau.Proofs.Y06StrictWeight
import Yau.Proofs.Y06DiagonalCoefficients

/-! The Jacobian determinant of an allowed map is constant because its
nonlinear variables are strictly lower in weight, including tied weights. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ}

def weightCode (w : Fin n → ℝ) (i : Fin n) : ℕ := weightRank w i * n + i.val

theorem weightCode_injective (w : Fin n → ℝ) : Function.Injective (weightCode w) := by
  intro i j hij
  apply Fin.ext
  have hmod := congrArg (fun t => t % n) hij
  simpa only [weightCode, Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero,
    Nat.zero_mod, zero_add, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hmod

theorem weightCode_strict {w : Fin n → ℝ} {i j : Fin n} (hij : w i < w j) :
    weightCode w i < weightCode w j := by
  have hrank := weightRank_strict hij
  calc
    weightCode w i < weightRank w i * n + n := Nat.add_lt_add_left i.isLt _
    _ = (weightRank w i + 1) * n := by ring
    _ ≤ weightRank w j * n := Nat.mul_le_mul_right n hrank
    _ ≤ weightCode w j := Nat.le_add_right _ _

theorem strict_weight_matrix_det {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (w : Fin n → ℝ)
    (hA : ∀ i j, i ≠ j → A i j ≠ 0 → w j < w i) : A.det = ∏ i, A i i := by
  let oldDecEq : DecidableEq (Fin n) := inferInstance
  letI : LinearOrder (Fin n) := LinearOrder.lift' (weightCode w) (weightCode_injective w)
  letI : LT (Fin n) := (inferInstance : LinearOrder (Fin n)).toLT
  letI : DecidableEq (Fin n) := oldDecEq
  have htri : A.IsLowerTriangular := by
    intro i j hij
    change weightCode w i < weightCode w j at hij
    by_contra hne
    have hneij : i ≠ j := by intro heq; subst j; exact (lt_irrefl _) hij
    have hcode := weightCode_strict (hA i j hneij hne)
    omega
  exact Matrix.det_of_isLowerTriangular A htri

theorem strict_variables_pderiv_zero {P : PolyMap n} {w : Fin n → ℝ}
    (hP : ∀ i j, j ∈ (P i).vars → w j < w i) (i j : Fin n) (hnot : ¬w j < w i) :
    pderiv j (P i) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hj
  exact hnot (hP i j hj)

theorem nonlinear_decomposition_apply (P : PolyMap n) (a : Fin n → ℂ)
    (hlinear : P.linearPart = Matrix.diagonal a) (i : Fin n) :
    P i = C (a i) * X i + nonlinearPart P i := by
  rw [← linearPolynomial_diagonal_apply, ← hlinear]
  change P i = linearPolynomial P.linearPart i + (P i - linearPolynomial P.linearPart i)
  abel

theorem strict_triangular_jacDet (P : PolyMap n) (a : Fin n → ℂ) (w : Fin n → ℝ)
    (hlinear : P.linearPart = Matrix.diagonal a)
    (hN : ∀ i j, j ∈ (nonlinearPart P i).vars → w j < w i) :
    P.jacDet = C (Matrix.diagonal a).det := by
  have hoff : ∀ i j, i ≠ j → jacobianMatrix P i j ≠ 0 → w j < w i := by
    intro i j hij hne
    by_contra hnot
    have hzero := strict_variables_pderiv_zero hN i j hnot
    apply hne
    change pderiv j (P i) = 0
    rw [nonlinear_decomposition_apply P a hlinear i, map_add, pderiv_C_mul, hzero]
    simp [pderiv_X, hij]
  have hdiag i : jacobianMatrix P i i = C (a i) := by
    have hzero := strict_variables_pderiv_zero hN i i (lt_irrefl _)
    change pderiv i (P i) = C (a i)
    rw [nonlinear_decomposition_apply P a hlinear i, map_add, pderiv_C_mul, hzero]
    simp
  change (jacobianMatrix P).det = _
  rw [strict_weight_matrix_det (jacobianMatrix P) w hoff]
  simp_rw [hdiag]
  rw [Matrix.det_diagonal, map_prod]

end Yau.Proofs.Y06Aux
