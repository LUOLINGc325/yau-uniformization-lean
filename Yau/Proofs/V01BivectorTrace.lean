import spec.CHAIN.CONTRACTS

/-! V01 scratch source: the actual four-index exterior-square cost is a
matrix trace. Change of frame is then exact cyclic-trace algebra. -/

noncomputable section
open Matrix
open scoped Matrix

namespace Yau.Blueprint.V01Proof

variable {n : ℕ}

theorem bivectorCost_eq_trace (A J : CotangentMatrix n) :
    bivectorCost A J = (1 / 2 : ℝ) * (A * J * Aᵀ * Jᴴ).trace.re := by
  have htrace : (A * J * Aᵀ * Jᴴ).trace =
      ∑ i, ∑ j, ∑ k, ∑ l, J i j * star (J k l) * A k i * A l j := by
    calc
      _ = ∑ k, ∑ l, ∑ j, ∑ i, A k i * J i j * A l j * star (J k l) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          Matrix.transpose_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
      _ = ∑ k, ∑ l, ∑ i, ∑ j, A k i * J i j * A l j * star (J k l) := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        exact Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ l, ∑ j, A k i * J i j * A l j * star (J k l) := by
        apply Finset.sum_congr rfl
        intro k _
        exact Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ l, ∑ j, A k i * J i j * A l j * star (J k l) :=
        Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ j, ∑ l, A k i * J i j * A l j * star (J k l) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        exact Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, ∑ l, A k i * J i j * A l j * star (J k l) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        ring
  rw [htrace]
  rfl

theorem bivectorCost_congruence (A J S : CotangentMatrix n) :
    bivectorCost (Sᴴ * A * S) J = bivectorCost A (S * J * Sᵀ) := by
  rw [bivectorCost_eq_trace, bivectorCost_eq_trace]
  have hST : (Sᴴ)ᵀ = (Sᵀ)ᴴ := rfl
  have htrace : ((Sᴴ * A * S) * J * (Sᴴ * A * S)ᵀ * Jᴴ).trace =
      (A * (S * J * Sᵀ) * Aᵀ * (S * J * Sᵀ)ᴴ).trace := by
    simpa only [Matrix.transpose_mul, Matrix.conjTranspose_mul, hST, Matrix.mul_assoc] using
      (Matrix.trace_mul_comm Sᴴ (A * S * J * Sᵀ * Aᵀ * (Sᴴ)ᵀ * Jᴴ))
  rw [htrace]

theorem bivectorCost_real_smul (r : ℝ) (A J : CotangentMatrix n) :
    bivectorCost ((r : ℂ) • A) J = r ^ 2 * bivectorCost A J := by
  rw [bivectorCost_eq_trace, bivectorCost_eq_trace]
  have htrace : (((r : ℂ) • A) * J * ((r : ℂ) • A)ᵀ * Jᴴ).trace =
      ((r ^ 2 : ℝ) : ℂ) * (A * J * Aᵀ * Jᴴ).trace := by
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.trace_smul, smul_eq_mul, Complex.ofReal_pow]
    ring
  rw [htrace]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

end Yau.Blueprint.V01Proof
