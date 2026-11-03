import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Scalar algebra retaining both the Harnack contribution and the nonnegative variance. -/

noncomputable section
open Set Filter
open scoped Topology

namespace Yau.Proofs.C04Aux

theorem log_rate_derivative_nonneg (t F N T V : ℝ) (ht : 0 < t) (hF : 0 < F)
    (hHarnack : 0 ≤ T + V + t⁻¹ * N) (hvariance : N ^ 2 ≤ F * V) :
    0 ≤ N / F + t * (((T + 2 * V) * F - N ^ 2) / F ^ 2) := by
  have hfirst : 0 ≤ (t * F) * (T + V + t⁻¹ * N) :=
    mul_nonneg (mul_pos ht hF).le hHarnack
  have hsecond : 0 ≤ t * (V * F - N ^ 2) := by
    apply mul_nonneg ht.le
    nlinarith
  have hidentity : (t * F) * (T + V + t⁻¹ * N) + t * (V * F - N ^ 2) =
      N * F + t * ((T + 2 * V) * F - N ^ 2) := by
    field_simp <;> ring
  have hnum : 0 ≤ N * F + t * ((T + 2 * V) * F - N ^ 2) :=
    hidentity ▸ add_nonneg hfirst hsecond
  have hquot : N / F + t * (((T + 2 * V) * F - N ^ 2) / F ^ 2) =
      (N * F + t * ((T + 2 * V) * F - N ^ 2)) / F ^ 2 := by
    field_simp <;> ring
  rw [hquot]
  exact div_nonneg hnum (sq_nonneg F)

/-- The endpoint derivative of a function convex in logarithmic time
dominates its secant, expressed directly in physical time. -/
theorem logarithmic_secant {L d : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hL : ∀ t, A ≤ t → HasDerivAt L (d t / t) t)
    (hd : MonotoneOn d (Ici A)) {u v : ℝ} (hu : A ≤ u) (huv : u ≤ v) :
    L v - L u ≤ d v * (Real.log v - Real.log u) := by
  have hv : A ≤ v := hu.trans huv
  have hanti : AntitoneOn (fun t => L t - d v * Real.log t) (Icc u v) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc u v)
    · intro t ht
      exact ((hL t (hu.trans ht.1)).continuousAt.sub
        ((Real.continuousAt_log (ne_of_gt (hA.trans_le (hu.trans ht.1)))).const_mul (d v))).continuousWithinAt
    · intro t ht
      have htuv : t ∈ Icc u v := interior_subset ht
      have htA : A ≤ t := hu.trans htuv.1
      exact ((hL t htA).sub ((Real.hasDerivAt_log (ne_of_gt (hA.trans_le htA))).const_mul (d v))).hasDerivWithinAt
    · intro t ht
      have htuv : t ∈ Icc u v := interior_subset ht
      have htA : A ≤ t := hu.trans htuv.1
      have htpos : 0 < t := hA.trans_le htA
      have hrate := hd htA hv htuv.2
      have hh := div_le_div_of_nonneg_right hrate htpos.le
      simpa only [div_eq_mul_inv, sub_nonpos] using hh
  have hh := hanti (left_mem_Icc.mpr huv) (right_mem_Icc.mpr huv) huv
  nlinarith

end Yau.Proofs.C04Aux
