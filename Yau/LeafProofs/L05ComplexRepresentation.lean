import Yau.LeafProofs.L22LeviBasic

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def secondFDerivMatrix {n : ℕ} (u : Space n → ℝ) (x : Space n) : Mat n :=
  fun i j => fderiv ℝ (fderiv ℝ u) x (realVec i) (realVec j)

theorem complexJ_conjugate_apply {n : ℕ} (A : Mat n) (i j : Fin n)
    (a b : Fin 2) :
    ((complexJ n).transpose * A * complexJ n) (i,a) (j,b) =
      (if a = 0 then 1 else -1) * (if b = 0 then 1 else -1) *
        A (i, if a = 0 then 1 else 0) (j, if b = 0 then 1 else 0) := by
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, complexJ,
      Fintype.sum_prod_type]

theorem hessian_space_eq_secondFDeriv {n : ℕ} {u : Space n → ℝ}
    {x : Space n} (hu : ContDiffAt ℝ 2 u x) :
    (hessian (fun p : Point n => u p.1) (x,0) : Mat n) =
      secondFDerivMatrix u x := by
  change ((selfAdjointPart ℝ
    (fun i j : RIdx n => fderiv ℝ (fderiv ℝ u) x (realVec i) (realVec j) : Mat n) :
      Sym n) : Mat n) = _
  apply IsSelfAdjoint.coe_selfAdjointPart_apply
  apply Matrix.isHermitian_iff_isSelfAdjoint.mp
  apply Matrix.IsHermitian.ext
  intro i j
  simpa only [star_trivial] using hu.isSymmSndFDerivAt (by norm_num) (realVec j) (realVec i)

/-- The real Hessian and the nested Wirtinger derivatives have exactly the
normalization required by the frozen L05 target. -/
theorem complexHessianRepresentation :
    Yau.ParabolicCandidates.ComplexHessianRepresentation := by
  intro n u x hu
  unfold complexHessianMap iota
  congr 1
  rw [hessian_space_eq_secondFDeriv hu]
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  rw [complexJ_conjugate_apply]
  have hs := hu.isSymmSndFDerivAt (by norm_num)
  have hre := (L18Aux.leviMatrix_entry_re_im hu stdVec i j).1
  have him := (L18Aux.leviMatrix_entry_re_im hu stdVec i j).2
  rw [hs (stdVec j) (stdVec i), hs (Complex.I • stdVec j) (Complex.I • stdVec i)] at hre
  rw [hs (stdVec j) (Complex.I • stdVec i), hs (Complex.I • stdVec j) (stdVec i)] at him
  fin_cases a <;> fin_cases b <;>
    simp [secondFDerivMatrix, leviC, hre, him, realVec, stdVec] <;>
    ring

end Yau.LeafProofs.L05Aux
