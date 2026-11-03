import Yau.Blueprint.Nodes

/-! Fixed polynomial factors are dominated by every positive square-root
exponential margin in the original volume clock. -/

open scoped Topology
open Filter

namespace Yau.NodeProofs.U02Proof

theorem polynomial_absorption_sqrt {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (C p : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ k in atTop, C * (1 + s k) ^ p ≤ Real.exp (eps * Real.sqrt (s k)) := by
  let u := fun k => Real.sqrt (1 + s k)
  have hshift : Tendsto (fun k => 1 + s k) atTop atTop := by
    apply tendsto_atTop.2
    intro R
    filter_upwards [(tendsto_atTop.1 hs) (R - 1)] with k hk
    linarith
  have hu : Tendsto u atTop atTop := Real.tendsto_sqrt_atTop.comp hshift
  have hbound : ∀ᶠ k in atTop,
      C ≤ Real.exp ((eps / 2) * u k) / (u k) ^ (2 * p) :=
    (tendsto_atTop.1
      ((tendsto_exp_mul_div_rpow_atTop (2 * p) (eps / 2) (by positivity)).comp hu)) C
  filter_upwards [hbound, (tendsto_atTop.1 hs) 1] with k hk hsk
  have hs0 : 0 ≤ s k := by linarith
  have hs1 : 0 < 1 + s k := by linarith
  have hu0 : 0 < u k := Real.sqrt_pos.mpr hs1
  have hu2 : u k ≤ 2 * Real.sqrt (s k) := by
    have ha := Real.sq_sqrt hs1.le
    have hb := Real.sq_sqrt hs0
    have hc := Real.sqrt_nonneg (1 + s k)
    have hd := Real.sqrt_nonneg (s k)
    dsimp [u]
    nlinarith
  have hpower : (1 + s k) ^ p = (u k) ^ (2 * p) := by
    calc
      (1 + s k) ^ p = (1 + s k) ^ ((2 * p) / 2) := by congr 1; ring
      _ = (u k) ^ (2 * p) := Real.rpow_div_two_eq_sqrt _ hs1.le
  rw [hpower]
  apply ((le_div_iff₀ (Real.rpow_pos_of_pos hu0 _)).mp hk).trans
  apply Real.exp_le_exp.mpr
  nlinarith

end Yau.NodeProofs.U02Proof
