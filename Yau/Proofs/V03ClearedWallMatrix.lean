import Yau.Proofs.V03ClearedWalls

/-! The polynomial reciprocal-wall matrix agrees with the actual scaled
Hessian where the cutoff is nonzero and is Hermitian through cutoff zeros. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem clearedReciprocalMatrix_eq {f : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (hne : f z ≠ 0) (dir : ι → E) {m : ℕ} (hm : 3 ≤ m) :
    clearedReciprocalMatrix f m dir z =
      ((f z : ℂ) ^ m) • leviMatrix (fun y => (f y)⁻¹) z dir := by
  ext a b
  simpa only [clearedReciprocalMatrix, leviMatrix, Complex.ofReal_inv, Matrix.smul_apply,
    smul_eq_mul, Function.comp_def, Complex.ofRealCLM_apply] using
    clearedReciprocalLevi_eq (hf.continuousLinearMap_comp Complex.ofRealCLM)
      (Complex.ofReal_ne_zero.mpr hne) (dir a) (dir b) hm

theorem clearedReciprocalMatrix_zero {f : E → ℝ} {z : E} (hz : f z = 0)
    (dir : ι → E) {m : ℕ} (hm : 4 ≤ m) : clearedReciprocalMatrix f m dir z = 0 := by
  ext a b
  simp only [clearedReciprocalMatrix, clearedReciprocalLevi, hz, Complex.ofReal_zero,
    zero_pow (by omega : m - 3 ≠ 0), zero_pow (by omega : m - 2 ≠ 0), mul_zero,
    zero_mul, sub_zero, Matrix.zero_apply]

theorem clearedReciprocalMatrix_isHermitian {f : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (dir : ι → E) {m : ℕ} (hm : 4 ≤ m) :
    (clearedReciprocalMatrix f m dir z).IsHermitian := by
  by_cases hz : f z = 0
  · rw [clearedReciprocalMatrix_zero hz dir hm]
    exact Matrix.isHermitian_zero
  · rw [clearedReciprocalMatrix_eq hf hz dir (by omega)]
    apply (leviMatrix_isHermitian (hf.inv hz) dir).smul
    simp [IsSelfAdjoint]

end Yau.Blueprint.V03Proof
