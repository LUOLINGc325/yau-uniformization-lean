import Yau.Proofs.U02Subexponential

/-! The jet order selected before the model constants gives the defect
margin on every late exponential raw ball. -/

open scoped Topology
open Filter

namespace Yau.NodeProofs.U02Proof

theorem eventually_exp_decay_lt {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    ∀ᶠ k in atTop, Real.exp (-a * s k) < R := by
  have hlim : Tendsto (fun k => Real.exp (-a * s k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hs.const_mul_atTop ha)
  exact hlim.eventually (gt_mem_nhds hR)

theorem eventual_jet_decay {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    {nu R : ℝ} {d : ℕ} (hR : 0 < R)
    (hd : 30 < ((d : ℝ) + 1) * nu) :
    ∀ᶠ k in atTop, ∀ r : ℝ, 0 ≤ r → r ≤ Real.exp (-5 * nu * s k) →
      Real.exp (s k) * (r / R) ^ (d + 1) ≤ Real.exp (-10 * s k) := by
  let a := 5 * nu * ((d : ℝ) + 1) - 1
  have ha : 10 < a := by dsimp [a]; nlinarith
  have hbound := subexponential_times_decay hs
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    ((1 / R) ^ (d + 1)) a 10 ha
  filter_upwards [hbound] with k hk
  intro r hr hrbound
  calc
    Real.exp (s k) * (r / R) ^ (d + 1) ≤
        Real.exp (s k) * (Real.exp (-5 * nu * s k) / R) ^ (d + 1) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (div_nonneg hr hR.le) (div_le_div_of_nonneg_right hrbound hR.le) _)
        (Real.exp_pos _).le
    _ = (1 / R) ^ (d + 1) * Real.exp (-a * s k) := by
      rw [div_pow, ← Real.exp_nat_mul, one_div, inv_pow]
      calc
        _ = (R ^ (d + 1))⁻¹ *
            (Real.exp (s k) * Real.exp (((d + 1 : ℕ) : ℝ) * (-5 * nu * s k))) := by ring
        _ = _ := by
          rw [← Real.exp_add]
          congr 2
          dsimp [a]
          push_cast
          ring
    _ ≤ _ := by simpa only [zero_mul, Real.exp_zero, mul_one] using hk

end Yau.NodeProofs.U02Proof
