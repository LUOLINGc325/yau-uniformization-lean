import Yau.Proofs.D06HardyParseval

/-! The actual unilateral shift and its left inverse on Hardy coefficients. -/

open scoped lp

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

def hardyShiftFn (a : HardySeq r) : ℕ × Fin r → ℂ :=
  fun k => match k.1 with
    | 0 => 0
    | n + 1 => a (n, k.2)

theorem hardyShift_summable (a : HardySeq r) :
    Summable (fun k : ℕ × Fin r => ‖hardyShiftFn a k‖ ^ 2) := by
  apply (summable_prod_of_nonneg (fun k => sq_nonneg ‖hardyShiftFn a k‖)).mpr
  refine ⟨fun n => (hasSum_fintype (fun j : Fin r => ‖hardyShiftFn a (n, j)‖ ^ 2)).summable, ?_⟩
  rw [← summable_nat_add_iff 1]
  simpa only [hardyShiftFn, Nat.add_one_sub_one] using (hardy_summable_norm_sq a).prod

def hardyShift (a : HardySeq r) : HardySeq r :=
  ⟨hardyShiftFn a, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hardyShift_summable a)⟩

@[simp] theorem hardyShift_zero (a : HardySeq r) (j : Fin r) :
    hardyShift a (0, j) = 0 := rfl

@[simp] theorem hardyShift_succ (a : HardySeq r) (n : ℕ) (j : Fin r) :
    hardyShift a (n + 1, j) = a (n, j) := rfl

theorem hardyTail_summable (a : HardySeq r) :
    Summable (fun k : ℕ × Fin r => ‖a (k.1 + 1, k.2)‖ ^ 2) := by
  apply (hardy_summable_norm_sq a).comp_injective
  intro k l h
  apply Prod.ext
  · exact Nat.add_right_cancel (Prod.mk.inj h).1
  · exact (Prod.mk.inj h).2

def hardyTail (a : HardySeq r) : HardySeq r :=
  ⟨fun k => a (k.1 + 1, k.2), memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hardyTail_summable a)⟩

@[simp] theorem hardyTail_apply (a : HardySeq r) (n : ℕ) (j : Fin r) :
    hardyTail a (n, j) = a (n + 1, j) := rfl

@[simp] theorem hardyTail_shift (a : HardySeq r) : hardyTail (hardyShift a) = a := by
  ext k
  exact hardyShift_succ a k.1 k.2

theorem hardyShift_tail (a : HardySeq r) (h0 : ∀ j, a (0, j) = 0) :
    hardyShift (hardyTail a) = a := by
  ext ⟨n, j⟩
  cases n with
  | zero => exact (h0 j).symm
  | succ n => rfl

@[simp] theorem hardyShift_add (a b : HardySeq r) :
    hardyShift (a + b) = hardyShift a + hardyShift b := by
  ext ⟨n, j⟩
  cases n <;> simp

@[simp] theorem hardyShift_smul (c : ℂ) (a : HardySeq r) :
    hardyShift (c • a) = c • hardyShift a := by
  ext ⟨n, j⟩
  cases n <;> simp

theorem hardyShift_norm_sq (a : HardySeq r) : ‖hardyShift a‖ ^ 2 = ‖a‖ ^ 2 := by
  rw [← hardy_column_norm_sum (hardyShift a), ← hardy_column_norm_sum a]
  apply Finset.sum_congr rfl
  intro j _
  have h := (hardy_column_summable_norm_sq (hardyShift a) j).tsum_eq_zero_add
  simpa only [hardyShift_zero, hardyShift_succ, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_add] using h

def hardyShiftLI : HardySeq r →ₗᵢ[ℂ] HardySeq r where
  toFun := hardyShift
  map_add' := hardyShift_add
  map_smul' := hardyShift_smul
  norm_map' a := by
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hardyShift_norm_sq a)

theorem hardyShiftLI_mem_range (a : HardySeq r) :
    a ∈ (hardyShiftLI : HardySeq r →ₗᵢ[ℂ] HardySeq r).range ↔ ∀ j, a (0, j) = 0 := by
  constructor
  · rintro ⟨b, rfl⟩ j
    exact hardyShift_zero b j
  · intro h0
    exact ⟨hardyTail a, hardyShift_tail a h0⟩

end Yau.NodeProofs.D06Aux
