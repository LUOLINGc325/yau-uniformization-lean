import spec.CHAIN.CONTRACTS

/-! Uncompiled F01 scratch definitions for the actual boundary blow-up
profile. No existence, regularity or geometry theorem is assumed here. -/
open scoped ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux

/-- Fixed explicit profile. On the source v<1 it is smooth, vanishes for
v≤1/2 and equals -2log(1-v) for v≥3/4. The corresponding proofs are to be
implemented against the actual pinned smoothTransition APIs after READY. -/
def conformalProfile (v : ℝ) : ℝ :=
  -2 * Real.smoothTransition (4 * v - 2) * Real.log (1 - v)

/-- Actual approximating conformal scalar, before restricting to its
regular sublevel manifold. -/
def conformalScalar {n : ℕ} {M : Yau.ComplexManifold n}
    (u : M.Carrier → ℝ) (L : ℝ) (x : M.Carrier) : ℝ :=
  conformalProfile (u x / L)

theorem conformalProfile_zero {v : ℝ} (hv : v ≤ 1 / 2) :
    conformalProfile v = 0 := by
  have hc : Real.smoothTransition (4 * v - 2) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  simp only [conformalProfile, hc, mul_zero, zero_mul]

theorem conformalProfile_log {v : ℝ} (hv : 3 / 4 ≤ v) :
    conformalProfile v = -2 * Real.log (1 - v) := by
  have hc : Real.smoothTransition (4 * v - 2) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  simp only [conformalProfile, hc, mul_one]

theorem conformalProfile_nonneg {v : ℝ} (hv : v < 1) :
    0 ≤ conformalProfile v := by
  by_cases hsmall : v ≤ 1 / 2
  · rw [conformalProfile_zero hsmall]
  · have hpos : 0 ≤ v := by linarith
    have hlog : Real.log (1 - v) ≤ 0 :=
      Real.log_nonpos (by linarith) (by linarith)
    have hc : 0 ≤ Real.smoothTransition (4 * v - 2) :=
      Real.smoothTransition.nonneg _
    unfold conformalProfile
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hlog

theorem conformalProfile_contDiffOn :
    ContDiffOn ℝ ∞ conformalProfile (Set.Iio 1) := by
  have hc : ContDiff ℝ ∞ (fun v : ℝ => Real.smoothTransition (4 * v - 2)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hl : ContDiffOn ℝ ∞ (fun v : ℝ => Real.log (1 - v)) (Set.Iio 1) :=
    ((contDiff_const.sub contDiff_id).contDiffOn).log
      (fun v hv => (sub_pos.mpr hv).ne')
  exact (contDiffOn_const.mul hc.contDiffOn).mul hl

/-- A finite conformal level stays a definite distance from u/L=1. This
is the scalar properness input, with no regular-value condition on u. -/
theorem conformalProfile_level_gap {v B : ℝ} (hv : v < 1)
    (hB : conformalProfile v ≤ B) :
    min (1 / 4) (Real.exp (-B / 2)) ≤ 1 - v := by
  by_cases hsmall : v ≤ 3 / 4
  · exact (min_le_left _ _).trans (by linarith)
  · have hlarge : 3 / 4 ≤ v := (lt_of_not_ge hsmall).le
    rw [conformalProfile_log hlarge] at hB
    have hlog : -B / 2 ≤ Real.log (1 - v) := by linarith
    have hexp := Real.exp_le_exp.mpr hlog
    have hδ : 0 < 1 - v := sub_pos.mpr hv
    exact (min_le_right _ _).trans (by simpa only [Real.exp_log hδ] using hexp)

end Yau.NodeProofs.F01Aux
