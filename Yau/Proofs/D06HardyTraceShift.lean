import Yau.Proofs.D06HardyShift

/-! Multiplication by a circle character realizes the actual Hardy shift on
the Fourier-defined L² trace, with all representative statements made AE. -/

open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardyPad_shift (a : HardySeq r) (j : Fin r) (n : ℤ) :
    hardyPad (hardyShift a) j n = hardyPad a j (n - 1) := by
  by_cases hn : 0 ≤ n
  · rw [hardyPad_apply (hardyShift a) j n, ite_eq_left hn]
    cases hnat : n.toNat with
    | zero =>
        have hn0 : n = 0 := by omega
        subst n
        simp
    | succ k =>
        have hp : 0 ≤ n - 1 := by omega
        have ht : (n - 1).toNat = k := by omega
        exact (hardyShift_succ a k j).trans (by
          symm
          rw [hardyPad_apply, ite_eq_left hp, ht])
  · rw [hardyPad_neg _ _ _ (by omega), hardyPad_neg _ _ _ (by omega)]

theorem fourierCoeff_character_mul (f : HardyCircle → ℂ) (k n : ℤ) :
    fourierCoeff (fun t => fourier k t * f t) n = fourierCoeff f (n - k) := by
  unfold fourierCoeff
  apply integral_congr_ae
  filter_upwards with t
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← fourier_add]
  rw [show -n + k = -(n - k) by ring]

theorem hardyCharMul_mem (k : ℤ) (f : Lp ℂ 2 hardyCircleMeasure) :
    MemLp (fun t : HardyCircle => fourier k t * f t) 2 hardyCircleMeasure := by
  have hchar : MemLp (fourier k : HardyCircle → ℂ) ⊤ hardyCircleMeasure :=
    ContinuousMap.memLp (p := ⊤) (μ := hardyCircleMeasure) ℂ (fourier k)
  exact hchar.fun_mul (Lp.memLp f)

def hardyCharMulLp (k : ℤ) (f : Lp ℂ 2 hardyCircleMeasure) : Lp ℂ 2 hardyCircleMeasure :=
  (hardyCharMul_mem k f).toLp (fun t : HardyCircle => fourier k t * f t)

theorem hardyCharMulLp_coe (k : ℤ) (f : Lp ℂ 2 hardyCircleMeasure) :
    hardyCharMulLp k f =ᵐ[hardyCircleMeasure] (fun t : HardyCircle => fourier k t * f t) :=
  (hardyCharMul_mem k f).coeFn_toLp

theorem hardyTraceLp_shift (a : HardySeq r) (j : Fin r) :
    hardyTraceLp (hardyShift a) j = hardyCharMulLp 1 (hardyTraceLp a j) := by
  apply (fourierBasis (T := 2 * Real.pi)).repr.injective
  ext n
  rw [fourierBasis_repr, fourierBasis_repr,
    fourierCoeff_congr_ae (hardyCharMulLp_coe 1 (hardyTraceLp a j)),
    fourierCoeff_character_mul, hardyTrace_fourierCoeff, hardyTrace_fourierCoeff]
  exact hardyPad_shift a j n

theorem hardyTrace_shift_ae (a : HardySeq r) (j : Fin r) :
    hardyTraceLp (hardyShift a) j =ᵐ[hardyCircleMeasure]
      (fun t : HardyCircle => fourier 1 t * hardyTraceLp a j t) := by
  rw [hardyTraceLp_shift]
  exact hardyCharMulLp_coe 1 (hardyTraceLp a j)

end Yau.NodeProofs.D06Aux
