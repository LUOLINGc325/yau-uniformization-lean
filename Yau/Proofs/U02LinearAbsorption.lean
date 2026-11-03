import Yau.Proofs.U02SqrtAbsorption

/-! Polynomial factors in the actual clock fit every positive linear
exponential margin, including the original natural-number power bounds. -/

open scoped Topology
open Filter

namespace Yau.NodeProofs.U02Proof

theorem polynomial_absorption {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (C p : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ k in atTop, C * (1 + s k) ^ p ≤ Real.exp (eps * s k) := by
  filter_upwards [polynomial_absorption_sqrt hs C p heps,
    (tendsto_atTop.1 hs) 1] with k hk hsk
  apply hk.trans
  apply Real.exp_le_exp.mpr
  have hroot : Real.sqrt (s k) ≤ s k := by
    have ha := Real.sq_sqrt (show 0 ≤ s k by linarith)
    have hb := Real.sqrt_nonneg (s k)
    nlinarith
  exact mul_le_mul_of_nonneg_left hroot heps.le

theorem nat_polynomial_absorption {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (C : ℝ) (p : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ k in atTop, C * (1 + s k) ^ p ≤ Real.exp (eps * s k) := by
  simpa only [Real.rpow_natCast] using polynomial_absorption hs C (p : ℝ) heps

end Yau.NodeProofs.U02Proof
