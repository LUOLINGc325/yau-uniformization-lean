import Yau.Proofs.Y03Grid

/-! A uniform lower gap on the literal grid in the actual macro-clock scale. -/

open scoped Topology
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

theorem uniform_grid_macro_lower (Q : ℕ → ℝ) (N : ℕ) (M : ℝ) {hm : ℝ} (hhm : 0 < hm) :
    ∃ J : ℕ, ∀ j₀, J ≤ j₀ → ∀ k,
      Real.sqrt (macroClock hm (macroAt Q N M hm j₀ k)) / 2 ≤
        gridClock Q N M hm j₀ (k + 1) - gridClock Q N M hm j₀ k := by
  have ha : 0 < Real.exp hm - 1 := sub_pos.2 (Real.one_lt_exp_iff.2 hhm)
  have hlim : Tendsto (fun j => (Real.exp hm - 1) * Real.sqrt (macroClock hm j)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop ha (Real.tendsto_sqrt_atTop.comp (macroClock_tendsto hm hhm))
  obtain ⟨J, hJ⟩ := (tendsto_atTop_atTop.1 hlim) 1
  refine ⟨J, ?_⟩
  intro j₀ hj₀ k
  rw [gridClock_succ_sub]
  apply (pieces_sqrt_bounds Q N M hm hhm _).1
  rw [macroClock_ratio]
  exact hJ _ (hj₀.trans (macroAt_mem Q N M hm j₀ k).1)

end Yau.Blueprint.Alignment.Y03Proof
