import Mathlib

/-! Scalar algebra and the value comparison in the smooth-majorant equation. -/

noncomputable section

namespace Yau.Proofs.F05Aux

def scalarNonlinearRHS (R D u : ℝ) : ℝ := Real.exp (-u) * D + (1 - Real.exp (-u)) * R

theorem scalarNonlinearRHS_eq (R D u : ℝ) :
    scalarNonlinearRHS R D u = R + Real.exp (-u) * (D - R) := by
  unfold scalarNonlinearRHS
  ring

theorem scalarNonlinearRHS_zero (R : ℝ) : scalarNonlinearRHS R 0 0 = 0 := by
  simp [scalarNonlinearRHS]

theorem scalarNonlinearRHS_le_scalar (R D u : ℝ) (hDR : D ≤ R) :
    scalarNonlinearRHS R D u ≤ R := by
  rw [scalarNonlinearRHS_eq]
  have hmul : Real.exp (-u) * (D - R) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr hDR)
  linarith

theorem hasDerivAt_scalarNonlinearRHS (R D u : ℝ) :
    HasDerivAt (scalarNonlinearRHS R D) (Real.exp (-u) * (R - D)) u := by
  have h := (((hasDerivAt_id u).neg.exp).mul_const (D - R)).const_add R
  convert h using 1
  · funext x
    exact scalarNonlinearRHS_eq R D x
  · simp only [Pi.neg_apply, id_eq]
    ring

theorem exp_neg_difference_le {u w : ℝ} (hw : 0 ≤ w) (hwu : w ≤ u) :
    0 ≤ Real.exp (-w) - Real.exp (-u) ∧ Real.exp (-w) - Real.exp (-u) ≤ u - w := by
  have hmono : Real.exp (-u) ≤ Real.exp (-w) := Real.exp_le_exp.mpr (by linarith)
  refine ⟨sub_nonneg.mpr hmono, ?_⟩
  have hdelta : 0 ≤ 1 - Real.exp (-(u - w)) := by
    have h := Real.exp_le_one_iff.mpr (show -(u - w) ≤ 0 by linarith)
    linarith
  have hupper : 1 - Real.exp (-(u - w)) ≤ u - w := by
    have h := Real.add_one_le_exp (-(u - w))
    linarith
  have hew : Real.exp (-w) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have heq : Real.exp (-w) - Real.exp (-u) =
      Real.exp (-w) * (1 - Real.exp (-(u - w))) := by
    rw [show -u = -w + -(u - w) by ring, Real.exp_add]
    ring
  rw [heq]
  simpa only [one_mul] using mul_le_mul hew hupper hdelta (show (0 : ℝ) ≤ 1 by norm_num)

theorem scalarNonlinearRHS_abs_sub_le (R D : ℝ) {u w : ℝ} (hw : 0 ≤ w) (hwu : w ≤ u) :
    |scalarNonlinearRHS R D u - scalarNonlinearRHS R D w| ≤ (u - w) * |R - D| := by
  have hd := exp_neg_difference_le hw hwu
  have heq : scalarNonlinearRHS R D u - scalarNonlinearRHS R D w =
      (Real.exp (-w) - Real.exp (-u)) * (R - D) := by
    unfold scalarNonlinearRHS
    ring
  rw [heq, abs_mul, abs_of_nonneg hd.1]
  exact mul_le_mul_of_nonneg_right hd.2 (abs_nonneg _)

theorem scalarNonlinearRHS_sub_le (R D A : ℝ) {u w : ℝ} (hw : 0 ≤ w) (hwu : w ≤ u)
    (hA : |R - D| ≤ A) :
    scalarNonlinearRHS R D u - scalarNonlinearRHS R D w ≤ A * (u - w) := by
  calc
    _ ≤ |scalarNonlinearRHS R D u - scalarNonlinearRHS R D w| := le_abs_self _
    _ ≤ (u - w) * |R - D| := scalarNonlinearRHS_abs_sub_le R D hw hwu
    _ ≤ (u - w) * A := mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr hwu)
    _ = _ := mul_comm _ _

/-- The residual in the zero-data fixed-point equation, with its actual terms. -/
def scalarResidual (p z Dpz Dp R pt : ℝ) : ℝ :=
  (Real.exp (-p - z) - Real.exp (-p)) * Dpz +
    (1 - Real.exp (-p - z)) * R - (pt - Real.exp (-p) * Dp)

/-- First equation compatibility makes every zero-initial iterate a compatible source. -/
theorem scalarResidual_initial (α R Dpz : ℝ) :
    scalarResidual α 0 Dpz 0 R ((1 - Real.exp (-α)) * R) = 0 := by
  simp [scalarResidual]

end Yau.Proofs.F05Aux
