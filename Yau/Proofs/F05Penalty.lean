import Mathlib

/-! A strict time penalty keeps upper contacts away from the terminal face. -/

noncomputable section

open scoped ContDiff

namespace Yau.Proofs.F05Aux

def comparisonPenalty (C S ε m t : ℝ) : ℝ :=
  Real.exp (C * t) * (m + ε / (S - t))

theorem comparisonPenalty_contDiffAt (C S ε m t : ℝ) (ht : t ≠ S) :
    ContDiffAt ℝ ∞ (comparisonPenalty C S ε m) t := by
  unfold comparisonPenalty
  exact ((contDiffAt_const.mul contDiffAt_id).exp).mul
    (contDiffAt_const.add (contDiffAt_const.div (contDiffAt_const.sub contDiffAt_id)
      (sub_ne_zero.mpr ht.symm)))

theorem comparisonPenalty_hasDerivAt (C S ε m t : ℝ) (ht : t ≠ S) :
    HasDerivAt (comparisonPenalty C S ε m)
      (C * comparisonPenalty C S ε m t + Real.exp (C * t) * ε / (S - t)^2) t := by
  have hden := (hasDerivAt_id t).const_sub S
  have hd := (hasDerivAt_const t ε).div hden (sub_ne_zero.mpr ht.symm)
  have he := ((hasDerivAt_id t).const_mul C).exp
  have hp := he.mul (hd.const_add m)
  convert hp using 1
  · rfl
  · simp only [comparisonPenalty, Pi.div_apply, id_eq]
    ring

theorem comparisonPenalty_slope (C S ε m t : ℝ) (hε : 0 ≤ ε) (ht : t < S) :
    C * comparisonPenalty C S ε m t ≤ deriv (comparisonPenalty C S ε m) t := by
  rw [(comparisonPenalty_hasDerivAt C S ε m t ht.ne).deriv]
  have hterm : 0 ≤ Real.exp (C * t) * ε / (S - t)^2 := by positivity
  linarith

theorem comparisonPenalty_pos (C S ε m t : ℝ) (hε : 0 < ε) (hm : 0 ≤ m)
    (ht : t < S) : 0 < comparisonPenalty C S ε m t := by
  unfold comparisonPenalty
  exact mul_pos (Real.exp_pos _) (add_pos_of_nonneg_of_pos hm (div_pos hε (sub_pos.mpr ht)))

/-- A fixed uniform bound makes the penalized difference nonpositive near the end. -/
theorem exists_terminal_penalty_time (S ε B t₀ : ℝ) (hε : 0 < ε) (ht₀ : t₀ < S) :
    ∃ s : ℝ, t₀ < s ∧ s < S ∧ B ≤ ε / (S - s) := by
  let d := min ((S - t₀) / 2) (ε / (2 * (|B| + 1)))
  have hd : 0 < d := lt_min (by linarith) (div_pos hε (by positivity))
  have hdT : d ≤ (S - t₀) / 2 := min_le_left _ _
  have hdB : d ≤ ε / (2 * (|B| + 1)) := min_le_right _ _
  refine ⟨S - d, by linarith, by linarith, ?_⟩
  rw [show S - (S - d) = d by ring]
  apply (le_div_iff₀ hd).mpr
  have hsmall : d * (2 * (|B| + 1)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 2 * (|B| + 1))).mp hdB
  have hb : B ≤ 2 * (|B| + 1) := by linarith [le_abs_self B, abs_nonneg B]
  nlinarith

end Yau.Proofs.F05Aux
