import Yau.Proofs.D06HardyShift

/-! Pure shift is verified on the actual nonnegative Hardy coefficients. -/

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardyShift_pow_lt (a : HardySeq r) (k n : ℕ) (hn : n < k) (j : Fin r) :
    ((hardyShiftLI : HardySeq r →ₗᵢ[ℂ] HardySeq r) ^ k) a (n, j) = 0 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
      rw [pow_succ']
      change hardyShift ((hardyShiftLI ^ k) a) (n, j) = 0
      cases n with
      | zero => exact hardyShift_zero _ _
      | succ n =>
          rw [hardyShift_succ]
          exact ih n (by omega)

theorem hardyShift_pure :
    (⨅ k : ℕ, ((hardyShiftLI : HardySeq r →ₗᵢ[ℂ] HardySeq r) ^ k).range) = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro a ha
  ext ⟨n, j⟩
  have hm := (Submodule.mem_iInf _).mp ha (n + 1)
  obtain ⟨b, hb⟩ := hm
  change a (n, j) = 0
  rw [← hb]
  exact hardyShift_pow_lt b (n + 1) n (Nat.lt_succ_self _) j

end Yau.NodeProofs.D06Aux
