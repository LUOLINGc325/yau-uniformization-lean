import Yau.Proofs.D06Elementary

/-! Ordinary Hardy vectors are actual square-summable nonnegative Fourier
coefficient arrays. Their circle traces use Mathlib's Fourier Hilbert basis. -/

open scoped lp
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

abbrev HardySeq (r : ℕ) := lp (fun _ : ℕ × Fin r => ℂ) 2
abbrev HardyCircle := AddCircle (2 * Real.pi)

instance hardyPeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev hardyCircleMeasure : Measure HardyCircle :=
  AddCircle.haarAddCircle

variable {r : ℕ}

theorem hardy_summable_norm_sq (a : HardySeq r) :
    Summable (fun k : ℕ × Fin r => ‖a k‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    ((lp.memℓp a).summable (by norm_num : 0 < (2 : ENNReal).toReal))

theorem hardy_column_summable_norm_sq (a : HardySeq r) (j : Fin r) :
    Summable (fun n : ℕ => ‖a (n, j)‖ ^ 2) := by
  exact (hardy_summable_norm_sq a).comp_injective fun _ _ h => (Prod.mk.inj h).1

def hardyPadFn (a : HardySeq r) (j : Fin r) (n : ℤ) : ℂ :=
  if 0 ≤ n then a (n.toNat, j) else 0

theorem hardyPad_mem (a : HardySeq r) (j : Fin r) : Memℓp (hardyPadFn a j) 2 := by
  apply memℓp_gen
  apply Summable.of_nat_of_neg_add_one
  · simpa only [hardyPadFn, Int.natCast_nonneg, ite_true, Int.toNat_natCast,
      ENNReal.toReal_ofNat, Real.rpow_two] using hardy_column_summable_norm_sq a j
  · have hz : (fun n : ℕ => ‖hardyPadFn a j (-(n + 1))‖ ^ (2 : ENNReal).toReal) =
        (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      unfold hardyPadFn
      rw [ite_eq_right (by omega)]
      norm_num
    rw [hz]
    exact summable_zero

def hardyPad (a : HardySeq r) (j : Fin r) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨hardyPadFn a j, hardyPad_mem a j⟩

@[simp] theorem hardyPad_apply (a : HardySeq r) (j : Fin r) (n : ℤ) :
    hardyPad a j n = if 0 ≤ n then a (n.toNat, j) else 0 := rfl

@[simp] theorem hardyPad_nat (a : HardySeq r) (j : Fin r) (n : ℕ) :
    hardyPad a j n = a (n, j) := by simp

theorem hardyPad_neg (a : HardySeq r) (j : Fin r) (n : ℤ) (hn : n < 0) :
    hardyPad a j n = 0 := by simp [not_le.mpr hn]

def hardyTraceLp (a : HardySeq r) (j : Fin r) : Lp ℂ 2 hardyCircleMeasure :=
  (fourierBasis (T := 2 * Real.pi)).repr.symm (hardyPad a j)

theorem hardyTrace_fourierCoeff (a : HardySeq r) (j : Fin r) (n : ℤ) :
    fourierCoeff (hardyTraceLp a j) n =
      if 0 ≤ n then a (n.toNat, j) else 0 := by
  rw [← fourierBasis_repr]
  simp only [hardyTraceLp, LinearIsometryEquiv.apply_symm_apply, hardyPad_apply]

@[simp] theorem hardyPad_negSucc (a : HardySeq r) (j : Fin r) (n : ℕ) :
    hardyPad a j (-(n + 1) : ℤ) = 0 := by
  apply hardyPad_neg
  omega

@[simp] theorem hardyPad_add (a b : HardySeq r) (j : Fin r) :
    hardyPad (a + b) j = hardyPad a j + hardyPad b j := by
  ext n
  by_cases hn : 0 ≤ n <;> simp [hn]

@[simp] theorem hardyPad_smul (c : ℂ) (a : HardySeq r) (j : Fin r) :
    hardyPad (c • a) j = c • hardyPad a j := by
  ext n
  by_cases hn : 0 ≤ n <;> simp [hn]

@[simp] theorem hardyTraceLp_add (a b : HardySeq r) (j : Fin r) :
    hardyTraceLp (a + b) j = hardyTraceLp a j + hardyTraceLp b j := by
  simp only [hardyTraceLp, hardyPad_add, map_add]

@[simp] theorem hardyTraceLp_smul (c : ℂ) (a : HardySeq r) (j : Fin r) :
    hardyTraceLp (c • a) j = c • hardyTraceLp a j := by
  simp only [hardyTraceLp, hardyPad_smul, map_smul]

theorem hardyPad_norm_sq (a : HardySeq r) (j : Fin r) :
    ‖hardyPad a j‖ ^ 2 = ∑' n : ℕ, ‖a (n, j)‖ ^ 2 := by
  have hn : Summable (fun n : ℕ => ‖hardyPad a j (n : ℤ)‖ ^ 2) := by
    simpa only [hardyPad_nat] using hardy_column_summable_norm_sq a j
  have hneg : Summable (fun n : ℕ => ‖hardyPad a j (-(n + 1) : ℤ)‖ ^ 2) := by
    simpa only [hardyPad_negSucc, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  have hp : ‖hardyPad a j‖ ^ 2 = ∑' n : ℤ, ‖hardyPad a j n‖ ^ 2 := by
    have h := lp.hasSum_norm (p := 2) (E := fun _ : ℤ => ℂ)
      (by norm_num : 0 < (2 : ENNReal).toReal) (hardyPad a j)
    have h' : HasSum (fun n : ℤ => ‖hardyPad a j n‖ ^ 2) (‖hardyPad a j‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
    exact h'.tsum_eq.symm
  have hsplit := tsum_of_nat_of_neg_add_one (f := fun n : ℤ => ‖hardyPad a j n‖ ^ 2) hn hneg
  apply hp.trans
  simpa only [hardyPad_nat, hardyPad_negSucc, norm_zero, zero_pow (by decide : 2 ≠ 0),
    tsum_zero, add_zero] using hsplit

theorem hardyTraceLp_norm_sq (a : HardySeq r) (j : Fin r) :
    ‖hardyTraceLp a j‖ ^ 2 = ∑' n : ℕ, ‖a (n, j)‖ ^ 2 := by
  simp only [hardyTraceLp, LinearIsometryEquiv.norm_map, hardyPad_norm_sq]

end Yau.NodeProofs.D06Aux
