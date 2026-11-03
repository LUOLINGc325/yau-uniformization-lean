import Yau.Proofs.V03ClearedLog
import Yau.Proofs.V03LeviMatrix

/-! The actual scaled log Levi matrix has a smooth polynomial expression
at every cutoff zero, with its original Hessian wherever the wall is nonzero. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def clearedLogMatrix (f : E → ℝ) (m : ℕ) (dir : ι → E) (z : E) : Matrix ι ι ℂ :=
  Matrix.of (fun a b => clearedLogLevi f m z (dir a) (dir b))

theorem clearedLogMatrix_eq {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z)
    (hne : f z ≠ 0) (dir : ι → E) {m : ℕ} (hm : 2 ≤ m) :
    clearedLogMatrix f m dir z = (f z : ℂ) ^ m •
      leviMatrix (fun y => Real.log (f y)) z dir := by
  ext a b
  exact clearedLogLevi_eq hf hne (dir a) (dir b) hm

theorem clearedLogMatrix_zero {f : E → ℝ} {z : E} (hz : f z = 0)
    (dir : ι → E) {m : ℕ} (hm : 3 ≤ m) :
    clearedLogMatrix f m dir z = 0 := by
  ext a b
  simp only [clearedLogMatrix, Matrix.of_apply, clearedLogLevi, hz, Complex.ofReal_zero,
    zero_pow (by omega : m - 1 ≠ 0), zero_pow (by omega : m - 2 ≠ 0),
    zero_mul, sub_zero, Matrix.zero_apply]

theorem clearedLogMatrix_entry_contDiffOn {U : Set E} (hU : IsOpen U)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) (dir : ι → E) (a b : ι) :
    ContDiffOn ℝ ∞ (fun z => clearedLogMatrix f m dir z a b) U :=
  clearedLogLevi_contDiffOn hU hf m (dir a) (dir b)

theorem clearedLogMatrix_isHermitian {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z)
    (dir : ι → E) {m : ℕ} (hm : 3 ≤ m) :
    (clearedLogMatrix f m dir z).IsHermitian := by
  by_cases hz : f z = 0
  · rw [clearedLogMatrix_zero hz dir hm]
    exact Matrix.isHermitian_zero
  rw [clearedLogMatrix_eq hf hz dir (by omega : 2 ≤ m)]
  apply (leviMatrix_isHermitian (hf.log hz) dir).smul
  simp [IsSelfAdjoint]

end Yau.Blueprint.V03Proof
