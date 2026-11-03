import Yau.Proofs.F03DyadicDerivativeBounds

/-! At every exhaustion value at least one, all active dyadic terms lie in three adjacent scales. -/
noncomputable section
open Set
namespace Yau.Proofs.F03Aux

theorem dyadicPartition_scale_support {s : ℝ} (hs : 1 ≤ s) (j : ℕ)
    (hj : dyadicPartition j s ≠ 0) :
    (2:ℝ)^j/2 ≤ s ∧ s ≤ 2*(2:ℝ)^j := by
  cases j with
  | zero =>
    constructor
    · norm_num
      linarith
    · have h : s < 2 := lt_of_not_ge (fun h => hj (dyadicProfile_zero h))
      simpa only [pow_zero,mul_one] using h.le
  | succ j =>
    have h := dyadicPartition_succ_tsupport j (subset_closure hj)
    rw [pow_succ,pow_succ] at *
    constructor <;> nlinarith [h.1,h.2]

theorem dyadicPartition_deriv_scale_support {s : ℝ} (hs : 1 ≤ s) (j : ℕ)
    (hj : deriv (dyadicPartition j) s ≠ 0) :
    (2:ℝ)^j/2 ≤ s ∧ s ≤ 2*(2:ℝ)^j := by
  cases j with
  | zero =>
    have h := dyadicProfile_deriv_tsupport (subset_closure hj)
    constructor <;> norm_num <;> linarith [h.1,h.2]
  | succ j =>
    have h := dyadicPartition_succ_deriv_tsupport j
      (subset_closure hj)
    rw [pow_succ,pow_succ] at *
    constructor <;> nlinarith [h.1,h.2]

theorem dyadicPartition_secondDeriv_scale_support {s : ℝ} (hs : 1 ≤ s) (j : ℕ)
    (hj : deriv (deriv (dyadicPartition j)) s ≠ 0) :
    (2:ℝ)^j/2 ≤ s ∧ s ≤ 2*(2:ℝ)^j := by
  cases j with
  | zero =>
    have h := (tsupport_deriv_subset.trans dyadicProfile_deriv_tsupport)
      (subset_closure hj)
    constructor <;> norm_num <;> linarith [h.1,h.2]
  | succ j =>
    have h := dyadicPartition_succ_secondDeriv_tsupport j
      (subset_closure hj)
    rw [pow_succ,pow_succ] at *
    constructor <;> nlinarith [h.1,h.2]

theorem dyadic_scale_band {s : ℝ} (hs : 1 ≤ s) :
    ∃ q : ℕ,(2:ℝ)^q ≤ s ∧ s < (2:ℝ)^(q+1) ∧
      ∀ j : ℕ,(2:ℝ)^j/2 ≤ s → s ≤ 2*(2:ℝ)^j → q ≤ j+1 ∧ j ≤ q+1 := by
  obtain ⟨q,hq,hq'⟩ := exists_nat_pow_near hs (by norm_num : (1:ℝ) < 2)
  refine ⟨q,hq,hq',fun j hLow hHigh => ⟨?_,?_⟩⟩
  · by_contra h
    have hPower := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show j+2 ≤ q by omega)
    have hPos : 0 < (2:ℝ)^j := by positivity
    simp only [pow_succ] at hPower
    nlinarith
  · by_contra h
    have hPower := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show q+2 ≤ j by omega)
    have hPos : 0 < (2:ℝ)^q := by positivity
    simp only [pow_succ] at hPower hq'
    nlinarith

theorem dyadicPartition_common_active_band {s : ℝ} (hs : 1 ≤ s) :
    ∃ q : ℕ,∀ j : ℕ,j+1 < q ∨ q+1 < j →
      dyadicPartition j s=0 ∧ deriv (dyadicPartition j) s=0 ∧
        deriv (deriv (dyadicPartition j)) s=0 := by
  obtain ⟨q,_hq,_hq',hBand⟩ := dyadic_scale_band hs
  refine ⟨q,fun j hj => ?_⟩
  have hExcluded : ¬ (q ≤ j+1 ∧ j ≤ q+1) := by omega
  refine ⟨?_,?_,?_⟩
  · by_contra h
    exact hExcluded (hBand j (dyadicPartition_scale_support hs j h).1
      (dyadicPartition_scale_support hs j h).2)
  · by_contra h
    exact hExcluded (hBand j (dyadicPartition_deriv_scale_support hs j h).1
      (dyadicPartition_deriv_scale_support hs j h).2)
  · by_contra h
    exact hExcluded (hBand j (dyadicPartition_secondDeriv_scale_support hs j h).1
      (dyadicPartition_secondDeriv_scale_support hs j h).2)

end Yau.Proofs.F03Aux
