import spec.CHAIN.CONTRACTS

/-! V01 scratch source: multiplicative clock errors are controlled before
the sign of the physical time derivative is known. -/

noncomputable section
open Filter
open scoped Topology

namespace Yau.Blueprint.V01Proof

theorem scaled_cost_upper (lam τ E β : ℝ) (hβ : 0 < β)
    (hlam : 0 ≤ lam) (hlamupper : lam ≤ 2)
    (hloss : |lam - 1| * (1 + |τ|) ≤ β / 4) (hE : E ≤ β / 4) :
    lam * (τ + E) ≤ τ + β := by
  have hτabs : (lam - 1) * τ ≤ |lam - 1| * |τ| := by
    simpa only [abs_mul] using le_abs_self ((lam - 1) * τ)
  have hτerr : (lam - 1) * τ ≤ β / 4 := by
    nlinarith [abs_nonneg (lam - 1)]
  have hEerr : lam * E ≤ β / 2 := by
    calc
      lam * E ≤ lam * (β / 4) := mul_le_mul_of_nonneg_left hE hlam
      _ ≤ 2 * (β / 4) := mul_le_mul_of_nonneg_right hlamupper (by positivity)
      _ = β / 2 := by ring
  nlinarith

theorem seqUpperZero_of_vanishing_upper
    {a b : ℕ → ℝ} (hb : Tendsto b atTop (𝓝 0))
    (hab : ∀ᶠ m in atTop, a m ≤ b m) : SeqUpperZero a := by
  intro r hr
  filter_upwards [hab, hb.eventually (gt_mem_nhds hr)] with m hm hmr
  exact hm.trans hmr.le

end Yau.Blueprint.V01Proof
