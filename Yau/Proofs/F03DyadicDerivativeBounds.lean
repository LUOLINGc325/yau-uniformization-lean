import Yau.Proofs.F03DyadicProfileDerivatives

/-! Actual derivative bounds and derivative supports of the fixed dyadic partition. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.Proofs.F03Aux

theorem dyadicPartition_succ_deriv (j : ℕ) (s : ℝ) :
    deriv (dyadicPartition (j+1)) s =
      deriv dyadicProfile (s/(2:ℝ)^(j+1))/(2:ℝ)^(j+1)-
      deriv dyadicProfile (s/(2:ℝ)^j)/(2:ℝ)^j := by
  change deriv (fun z => dyadicProfile (z/(2:ℝ)^(j+1))-dyadicProfile (z/(2:ℝ)^j)) s=_
  have hD (R : ℝ) := (dyadicProfile_contDiff.differentiable (by simp) (s/R)).hasDerivAt.comp s
    ((hasDerivAt_id s).div_const R)
  simpa only [Function.comp_def,id_eq,Pi.sub_def,mul_one_div] using
    ((hD ((2:ℝ)^(j+1))).sub (hD ((2:ℝ)^j))).deriv

theorem dyadicPartition_succ_secondDeriv (j : ℕ) (s : ℝ) :
    deriv (deriv (dyadicPartition (j+1))) s =
      deriv (deriv dyadicProfile) (s/(2:ℝ)^(j+1))/((2:ℝ)^(j+1))^2-
      deriv (deriv dyadicProfile) (s/(2:ℝ)^j)/((2:ℝ)^j)^2 := by
  have hd : ContDiff ℝ ∞ (deriv dyadicProfile) :=
    (contDiff_infty_iff_deriv.mp dyadicProfile_contDiff).2
  rw [show deriv (dyadicPartition (j+1))=(fun z =>
      deriv dyadicProfile (z/(2:ℝ)^(j+1))/(2:ℝ)^(j+1)-
      deriv dyadicProfile (z/(2:ℝ)^j)/(2:ℝ)^j) from funext (dyadicPartition_succ_deriv j)]
  have hD (R : ℝ) : HasDerivAt (fun z => deriv dyadicProfile (z/R)/R)
      (deriv (deriv dyadicProfile) (s/R)/R^2) s := by
    have h := ((hd.differentiable (by simp) (s/R)).hasDerivAt.comp s
      ((hasDerivAt_id s).div_const R)).div_const R
    convert h using 1 <;> simp only [Function.comp_def,id_eq,mul_one_div,div_div,← pow_two]
  exact ((hD ((2:ℝ)^(j+1))).sub (hD ((2:ℝ)^j))).deriv

theorem dyadicPartition_derivative_bounds :
    ∃ B : ℝ,0 < B ∧ ∀ j : ℕ,∀ s : ℝ,
      |deriv (dyadicPartition j) s| ≤ B/(2:ℝ)^j ∧
      |deriv (deriv (dyadicPartition j)) s| ≤ B/((2:ℝ)^j)^2 := by
  obtain ⟨B,hB,hBound⟩ := dyadicProfile_derivative_bounds
  refine ⟨5*B,by positivity,fun j s => ?_⟩
  cases j with
  | zero =>
    rw [show dyadicPartition 0=dyadicProfile from rfl]
    simp only [pow_zero,one_pow,div_one]
    exact ⟨(hBound s).1.trans (by linarith),(hBound s).2.trans (by linarith)⟩
  | succ j =>
    have hP : 0 < (2:ℝ)^j := by positivity
    have hP' : 0 < (2:ℝ)^(j+1) := by positivity
    constructor
    · rw [dyadicPartition_succ_deriv]
      calc
        _ ≤ |deriv dyadicProfile (s/(2:ℝ)^(j+1))/(2:ℝ)^(j+1)|+
            |deriv dyadicProfile (s/(2:ℝ)^j)/(2:ℝ)^j| := abs_sub _ _
        _ = |deriv dyadicProfile (s/(2:ℝ)^(j+1))|/(2:ℝ)^(j+1)+
            |deriv dyadicProfile (s/(2:ℝ)^j)|/(2:ℝ)^j := by
          rw [abs_div,abs_div,abs_of_pos hP,abs_of_pos hP']
        _ ≤ B/(2:ℝ)^(j+1)+B/(2:ℝ)^j := add_le_add
          (div_le_div_of_nonneg_right (hBound _).1 hP'.le)
          (div_le_div_of_nonneg_right (hBound _).1 hP.le)
        _ ≤ (5*B)/(2:ℝ)^(j+1) := by rw [pow_succ];field_simp;nlinarith
    · rw [dyadicPartition_succ_secondDeriv]
      calc
        _ ≤ |deriv (deriv dyadicProfile) (s/(2:ℝ)^(j+1))/((2:ℝ)^(j+1))^2|+
            |deriv (deriv dyadicProfile) (s/(2:ℝ)^j)/((2:ℝ)^j)^2| := abs_sub _ _
        _ = |deriv (deriv dyadicProfile) (s/(2:ℝ)^(j+1))|/((2:ℝ)^(j+1))^2+
            |deriv (deriv dyadicProfile) (s/(2:ℝ)^j)|/((2:ℝ)^j)^2 := by
          rw [abs_div,abs_div,abs_of_nonneg (sq_nonneg ((2:ℝ)^(j+1))),abs_of_nonneg (sq_nonneg ((2:ℝ)^j))]
        _ ≤ B/((2:ℝ)^(j+1))^2+B/((2:ℝ)^j)^2 := add_le_add
          (div_le_div_of_nonneg_right (hBound _).2 (sq_nonneg _))
          (div_le_div_of_nonneg_right (hBound _).2 (sq_nonneg _))
        _ = (5*B)/((2:ℝ)^(j+1))^2 := by rw [pow_succ];field_simp <;> ring

theorem dyadicPartition_succ_tsupport (j : ℕ) :
    tsupport (dyadicPartition (j+1)) ⊆ Icc ((2:ℝ)^j) ((2:ℝ)^(j+2)) := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  exact ⟨le_of_not_gt (fun h => hs (dyadicPartition_succ_zero_below j h.le)),
    le_of_not_gt (fun h => hs (dyadicPartition_succ_zero_above j h.le))⟩

theorem dyadicPartition_succ_deriv_tsupport (j : ℕ) :
    tsupport (deriv (dyadicPartition (j+1))) ⊆ Icc ((2:ℝ)^j) ((2:ℝ)^(j+2)) :=
  tsupport_deriv_subset.trans (dyadicPartition_succ_tsupport j)

theorem dyadicPartition_succ_secondDeriv_tsupport (j : ℕ) :
    tsupport (deriv (deriv (dyadicPartition (j+1)))) ⊆ Icc ((2:ℝ)^j) ((2:ℝ)^(j+2)) :=
  tsupport_deriv_subset.trans (dyadicPartition_succ_deriv_tsupport j)

end Yau.Proofs.F03Aux
