import Yau.Proofs.V03ClearedLog
import Yau.Proofs.V03WirtingerDirections
import Yau.Proofs.V03AmbientTensorAlgebra

/-! The actual scaled log differential has a smooth polynomial covector
representative, and the Gram inverse transports covectors without a rank
exception. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem wirt_log_real {f : E → ℝ} {z : E} (hf : DifferentiableAt ℝ f z)
    (hne : f z ≠ 0) (v : E) :
    wirt (fun y => (Real.log (f y) : ℂ)) z v = (f z : ℂ)⁻¹ * wirt (fun y => (f y : ℂ)) z v := by
  simp only [wirt, fderiv_ofReal_apply (hf.log hne), fderiv_ofReal_apply hf,
    fderiv.log hf hne, smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
  ring

def clearedLogCovector (f : E → ℝ) (a : ℕ) (dir : ι → E) (z : E) : ι → ℂ :=
  fun i => (f z : ℂ) ^ (a - 1) * wirt (fun y => (f y : ℂ)) z (dir i)

theorem clearedLogCovector_eq {f : E → ℝ} {z : E} (hf : DifferentiableAt ℝ f z)
    (hne : f z ≠ 0) (a : ℕ) (ha : 1 ≤ a) (dir : ι → E) :
    clearedLogCovector f a dir z =
      (f z : ℂ) ^ a • (fun i => wirt (fun y => (Real.log (f y) : ℂ)) z (dir i)) := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul, wirt_log_real hf hne]
  unfold clearedLogCovector
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  simp only [Nat.add_sub_cancel_left, pow_add, pow_one]
  field_simp [Complex.ofReal_ne_zero.mpr hne]

theorem clearedLogCovector_zero {f : E → ℝ} {z : E} (hz : f z = 0)
    (a : ℕ) (ha : 2 ≤ a) (dir : ι → E) : clearedLogCovector f a dir z = 0 := by
  funext i
  simp only [clearedLogCovector, hz, Complex.ofReal_zero, zero_pow (by omega : a - 1 ≠ 0),
    zero_mul, Pi.zero_apply]

theorem clearedLogCovector_entry_contDiffOn {U : Set E} (hU : IsOpen U)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (a : ℕ) (dir : ι → E) (i : ι) :
    ContDiffOn ℝ ∞ (fun z => clearedLogCovector f a dir z i) U :=
  ((Complex.ofRealCLM.contDiff.comp_contDiffOn hf).pow (a - 1)).mul
    (wirt_contDiffOn hU (Complex.ofRealCLM.contDiff.comp_contDiffOn hf) (dir i))

def ambientCovector {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix κ ι ℂ) (w : ι → ℂ) : κ → ℂ := w ᵥ* gramLeftInverse A

theorem ambientCovector_contract {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {A : Matrix κ ι ℂ} (hA : IsUnit (Aᴴ * A)) (w v : ι → ℂ) :
    ambientCovector A w ⬝ᵥ (A *ᵥ v) = w ⬝ᵥ v := by
  rw [ambientCovector, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    gramLeftInverse_mul hA, Matrix.one_mulVec]

theorem ambientCovector_covariant {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix κ ι ℂ) (w : ι → ℂ) (S : Matrix ι ι ℂ) (hS : IsUnit S) :
    ambientCovector (A * S) (w ᵥ* S) = ambientCovector A w := by
  unfold ambientCovector
  rw [gramLeftInverse_right_mul A S hS, Matrix.vecMul_vecMul, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS), Matrix.one_mul]

end Yau.Blueprint.V03Proof
