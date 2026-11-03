import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! A genuine smooth dyadic partition with nonnegative coefficients and an exact finite sum. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.Proofs.F03Aux

def dyadicProfile (s : ℝ) : ℝ := 1-Real.smoothTransition (s-1)

theorem dyadicProfile_contDiff : ContDiff ℝ ∞ dyadicProfile :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem dyadicProfile_range (s : ℝ) : 0 ≤ dyadicProfile s ∧ dyadicProfile s ≤ 1 := by
  dsimp [dyadicProfile]
  constructor <;> linarith [Real.smoothTransition.nonneg (s-1),Real.smoothTransition.le_one (s-1)]

theorem dyadicProfile_antitone : Antitone dyadicProfile := by
  intro s t hst
  have hh := Real.smoothTransition.monotone (sub_le_sub_right hst 1)
  dsimp [dyadicProfile]
  linarith

theorem dyadicProfile_one {s : ℝ} (hs : s ≤ 1) : dyadicProfile s=1 := by
  rw [dyadicProfile,Real.smoothTransition.zero_of_nonpos (by linarith),sub_zero]

theorem dyadicProfile_zero {s : ℝ} (hs : 2 ≤ s) : dyadicProfile s=0 := by
  rw [dyadicProfile,Real.smoothTransition.one_of_one_le (by linarith),sub_self]

def dyadicPartition : ℕ → ℝ → ℝ
  | 0,s => dyadicProfile s
  | j+1,s => dyadicProfile (s/(2:ℝ)^(j+1))-dyadicProfile (s/(2:ℝ)^j)

theorem dyadicPartition_contDiff (j : ℕ) : ContDiff ℝ ∞ (dyadicPartition j) := by
  cases j with
  | zero => exact dyadicProfile_contDiff
  | succ j =>
    change ContDiff ℝ ∞ (fun s => dyadicProfile (s/(2:ℝ)^(j+1))-dyadicProfile (s/(2:ℝ)^j))
    exact (dyadicProfile_contDiff.comp (contDiff_id.div_const _)).sub
      (dyadicProfile_contDiff.comp (contDiff_id.div_const _))

theorem dyadicPartition_nonnegative (j : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ dyadicPartition j s := by
  cases j with
  | zero => exact (dyadicProfile_range s).1
  | succ j =>
    apply sub_nonneg.mpr
    apply dyadicProfile_antitone
    exact div_le_div_of_nonneg_left hs (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_succ j))

theorem dyadicPartition_succ_zero_below (j : ℕ) {s : ℝ} (hs : s ≤ (2:ℝ)^j) :
    dyadicPartition (j+1) s=0 := by
  have h1 : s/(2:ℝ)^j ≤ 1 := (div_le_one (by positivity)).mpr hs
  have h2 : s/(2:ℝ)^(j+1) ≤ 1 := (div_le_one (by positivity)).mpr
    (hs.trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_succ j)))
  simp only [dyadicPartition,dyadicProfile_one h1,dyadicProfile_one h2,sub_self]

theorem dyadicPartition_succ_zero_above (j : ℕ) {s : ℝ} (hs : (2:ℝ)^(j+2) ≤ s) :
    dyadicPartition (j+1) s=0 := by
  have h1 : 2 ≤ s/(2:ℝ)^j := (le_div_iff₀ (by positivity)).mpr (by
    rw [pow_add] at hs
    norm_num at hs
    have hp : 0 ≤ (2:ℝ)^j := by positivity
    nlinarith)
  have h2 : 2 ≤ s/(2:ℝ)^(j+1) := (le_div_iff₀ (by positivity)).mpr (by
    simpa only [pow_succ,mul_comm] using hs)
  simp only [dyadicPartition,dyadicProfile_zero h1,dyadicProfile_zero h2,sub_self]

theorem dyadicPartition_sum (N : ℕ) (s : ℝ) :
    (∑ j ∈ Finset.range (N+1),dyadicPartition j s)=dyadicProfile (s/(2:ℝ)^N) := by
  induction N with
  | zero => simp [dyadicPartition]
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [dyadicPartition]
    ring

theorem dyadicPartition_sum_one {N : ℕ} {s : ℝ} (hs : s ≤ (2:ℝ)^N) :
    (∑ j ∈ Finset.range (N+1),dyadicPartition j s)=1 := by
  rw [dyadicPartition_sum]
  exact dyadicProfile_one ((div_le_one (by positivity)).mpr hs)

theorem dyadicPartition_locally_eventually_zero (s : ℝ) :
    ∃ N : ℕ,∃ V : Set ℝ,IsOpen V ∧ s ∈ V ∧ ∀ j,N ≤ j → ∀ t ∈ V,dyadicPartition j t=0 := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  have hPower : (N:ℝ) < (2:ℝ)^N := by exact_mod_cast N.lt_two_pow_self
  refine ⟨N+1,Iio ((2:ℝ)^N),isOpen_Iio,hN.trans hPower,?_⟩
  intro j hj t ht
  cases j with
  | zero => omega
  | succ j =>
    apply dyadicPartition_succ_zero_below
    exact ht.le.trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega))

end Yau.Proofs.F03Aux
