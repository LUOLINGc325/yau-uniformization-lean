import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! The exact two-term Leibniz estimate for a linear factor. There is no
order-dependent multiplier on the highest derivative of the coefficient. -/

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_id_zero (m : ℕ) (hm : 2 ≤ m) (x : E) :
    ‖iteratedFDeriv ℝ m (id : E → E) x‖ = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  rw [← norm_iteratedFDeriv_fderiv]
  have hD : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E := by
    funext y
    exact fderiv_id
  rw [hD, iteratedFDeriv_const_of_ne (show j ≠ 0 by omega)]
  simp only [Pi.zero_apply, norm_zero]

theorem norm_iteratedFDeriv_apply_identity_le
    (T : E → E →L[ℝ] F) (hT : ContDiff ℝ ∞ T) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ (k + 1) (fun y => T y y) x‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) T x‖ * ‖x‖ +
        ((k : ℝ) + 1) * ‖iteratedFDeriv ℝ k T x‖ := by
  have hbase := norm_iteratedFDeriv_clm_apply hT
    (contDiff_id : ContDiff ℝ ∞ (id : E → E)) x
    (show ((k + 1 : ℕ) : ℕ∞ω) ≤ ∞ by simp)
  have hsum :
      (∑ i ∈ Finset.range (k + 1), ((k + 1).choose i : ℝ) *
        ‖iteratedFDeriv ℝ i T x‖ * ‖iteratedFDeriv ℝ (k + 1 - i) (id : E → E) x‖) =
      ((k : ℝ) + 1) * ‖iteratedFDeriv ℝ k T x‖ *
        ‖iteratedFDeriv ℝ 1 (id : E → E) x‖ := by
    calc
      _ = ((k + 1).choose k : ℝ) * ‖iteratedFDeriv ℝ k T x‖ *
          ‖iteratedFDeriv ℝ (k + 1 - k) (id : E → E) x‖ := by
        apply Finset.sum_eq_single k
        · intro i hi hik
          have hi' := Finset.mem_range.mp hi
          rw [norm_iteratedFDeriv_id_zero _ (by omega)]
          exact mul_zero _
        · intro hk
          exact (hk (Finset.mem_range.mpr (Nat.lt_succ_self k))).elim
      _ = _ := by
        have hIndex : k + 1 - k = 1 := by omega
        rw [hIndex]
        simp only [Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one]
  rw [Finset.sum_range_succ, hsum] at hbase
  have hEnd : k + 1 - (k + 1) = 0 := Nat.sub_self _
  rw [hEnd, norm_iteratedFDeriv_zero] at hbase
  simp only [Nat.choose_self, Nat.cast_one, one_mul, id_eq] at hbase
  have hid : ‖iteratedFDeriv ℝ 1 (id : E → E) x‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_one, fderiv_id]
    exact ContinuousLinearMap.norm_id_le
  have hlast : ((k : ℝ) + 1) * ‖iteratedFDeriv ℝ k T x‖ *
      ‖iteratedFDeriv ℝ 1 (id : E → E) x‖ ≤
        ((k : ℝ) + 1) * ‖iteratedFDeriv ℝ k T x‖ :=
    mul_le_of_le_one_right (by positivity) hid
  exact hbase.trans (by linarith)

end Yau.Blueprint.C02Proof
