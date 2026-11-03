import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-! One-dimensional clock estimates used in the Ricci-window argument. -/

noncomputable section
open Filter Set
open scoped Topology

namespace Yau.Proofs.C04Aux

/-- A fixed positive lower bound for t s'(t) forces the original clock to diverge. -/
theorem tendsto_clock_of_speed_lower {s r : ℝ → ℝ} {A c : ℝ}
    (hA : 0 < A) (hc : 0 < c)
    (hd : ∀ t, A ≤ t → HasDerivAt s (r t) t)
    (hb : ∀ t, A ≤ t → c ≤ t * r t) : Tendsto s atTop atTop := by
  let f := fun t => s t - c * Real.log t
  have hmono : MonotoneOn f (Ici A) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici A)
    · intro t ht
      exact ((hd t ht).continuousAt.sub
        ((Real.continuousAt_log (ne_of_gt (hA.trans_le ht))).const_mul c)).continuousWithinAt
    · intro t ht
      have htA : A ≤ t := interior_subset ht
      exact ((hd t htA).sub ((Real.hasDerivAt_log
        (ne_of_gt (hA.trans_le htA))).const_mul c)).hasDerivWithinAt
    · intro t ht
      have htA : A ≤ t := interior_subset ht
      have htpos : 0 < t := hA.trans_le htA
      have hb' := hb t htA
      apply (mul_nonneg_iff_of_pos_right htpos).mp
      simpa only [sub_mul, mul_assoc, inv_mul_cancel₀ htpos.ne', mul_one, mul_comm t] using
        (sub_nonneg.mpr hb')
  have hlow : (fun t => c * Real.log t + f A) ≤ᶠ[atTop] s := by
    filter_upwards [eventually_ge_atTop A] with t ht
    have hh := hmono (le_refl A) ht ht
    dsimp [f] at *
    linarith
  exact tendsto_atTop_mono' atTop hlow
    ((Real.tendsto_log_atTop.const_mul_atTop hc).atTop_add (tendsto_const_nhds (x := f A)))

/-- The contradiction behind liminf q/s <= 2: growth faster than the
quadratic power is incompatible with the given linear-in-time clock bound. -/
theorem exists_speed_le_twice_clock {s r : ℝ → ℝ}
    (hd : ∀ t, 0 < t → HasDerivAt s (r t) t)
    (hinf : Tendsto s atTop atTop)
    (hupper : ∃ C : ℝ, ∀ t, 0 ≤ t → s t ≤ C * (1 + t))
    (T : ℝ) : ∃ t, T ≤ t ∧ t * r t ≤ 2 * s t := by
  by_contra hn
  push_neg at hn
  obtain ⟨C, hC⟩ := hupper
  obtain ⟨B, hB⟩ := (tendsto_atTop_atTop.1 hinf) 1
  let A := max 1 (max B T)
  have hAone : 1 ≤ A := le_max_left _ _
  have hA : 0 < A := zero_lt_one.trans_le hAone
  have hAT : T ≤ A := (le_max_right B T).trans (le_max_right 1 _)
  have hsA : 0 < s A := zero_lt_one.trans_le
    (hB A ((le_max_left B T).trans (le_max_right 1 _)))
  let f := fun t => s t / t ^ 2
  let c := f A
  have hc : 0 < c := div_pos hsA (sq_pos_of_pos hA)
  have hmono : MonotoneOn f (Ici A) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici A)
    · intro t ht
      exact ((hd t (hA.trans_le ht)).continuousAt.div
        (continuousAt_id.pow 2) (pow_ne_zero 2 (ne_of_gt (hA.trans_le ht)))).continuousWithinAt
    · intro t ht
      have htA : A ≤ t := interior_subset ht
      exact ((hd t (hA.trans_le htA)).div ((hasDerivAt_id t).pow 2)
        (pow_ne_zero 2 (ne_of_gt (hA.trans_le htA)))).hasDerivWithinAt
    · intro t ht
      have htA : A ≤ t := interior_subset ht
      have htpos : 0 < t := hA.trans_le htA
      have hh := hn t (hAT.trans htA)
      apply div_nonneg _ (sq_nonneg _)
      simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
      nlinarith
  let t := max A (2 * |C| / c + 1)
  have htA : A ≤ t := le_max_left _ _
  have htone : 1 ≤ t := hAone.trans htA
  have htpos : 0 < t := hA.trans_le htA
  have hlower : c * t ^ 2 ≤ s t := by
    exact (le_div_iff₀ (sq_pos_of_pos htpos)).mp
      (hmono (le_refl A) htA htA)
  have hupper' : s t ≤ 2 * |C| * t := calc
    s t ≤ C * (1 + t) := hC t htpos.le
    _ ≤ |C| * (1 + t) := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
    _ ≤ 2 * |C| * t := by nlinarith [abs_nonneg C]
  have htlower : 2 * |C| / c + 1 ≤ t := le_max_right _ _
  have hstrict : 2 * |C| < c * t := by
    have hh := mul_le_mul_of_nonneg_left htlower hc.le
    rw [mul_add, mul_div_cancel₀ _ hc.ne', mul_one] at hh
    linarith
  nlinarith

end Yau.Proofs.C04Aux
