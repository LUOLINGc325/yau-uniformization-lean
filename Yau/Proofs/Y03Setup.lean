import Yau.Proofs.Y03Clock
import Yau.Proofs.Y03Grid
import Yau.Proofs.Y03Frames

/-! The clock, canonical grid, actual singular frames and exact trace, on the same witnesses. -/

open scoped Topology
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

theorem exists_window_length {hm a₀ : ℝ} (hhm : 0 < hm) (ha₀ : 0 < a₀) :
    ∃ N : ℕ, 1 ≤ N ∧ Real.exp (-hm * N) ≤ a₀ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (-Real.log a₀ / hm))
  have hN₁ : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hlog : -Real.log a₀ < hm * (N : ℝ) := by
    simpa only [mul_comm] using
      (div_lt_iff₀ hhm).1 ((le_max_right _ _).trans_lt hN)
  refine ⟨N, by exact_mod_cast hN₁.le, ?_⟩
  calc
    Real.exp (-hm * N) ≤ Real.exp (Real.log a₀) := Real.exp_le_exp.2 (by linarith)
    _ = a₀ := Real.exp_log ha₀

theorem clock_grid_singularFrames {n : ℕ} {X : KahlerManifold n}
    (o : Pt X) (h : Flow X) (ρ : STF X) {r₀ r₁ σ C Cb t₀ : ℝ}
    {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n}
    (hWindows : RicciWindows X o h ρ)
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f) :
    ∃ (time : ℝ → ℝ) (s₀ a₀ b₀ : ℝ), ClockParameter X o h ρ time s₀ ∧
      0 < a₀ ∧ a₀ < 1 ∧ 0 < b₀ ∧ ClockRateInput o h time s₀ a₀ b₀ ∧
      (∀ s, s₀ ≤ s → 0 < time (a₀ * s) ∧ ρ o (time (a₀ * s)) = a₀ * s) ∧
      ∀ hm, 0 < hm → hm < 1 → ∃ N : ℕ, 1 ≤ N ∧ Real.exp (-hm * N) ≤ a₀ ∧
        ∀ M : ℝ, 0 < M → ∃ jLate : ℕ, 2 * N < jLate ∧
          s₀ ≤ macroClock hm (jLate - 2 * N) ∧
          ∀ j₀, jLate ≤ j₀ →
            let Q := sampledSpeed o h time hm
            let s := gridClock Q N M hm j₀
            let tk := fun k => time (s k)
            GridLayout Q N M hm j₀ ∧ (∀ k, s₀ ≤ s k ∧ t₀ ≤ tk k) ∧
              ∃ E : Frames n, SingularFrames F tk E ∧
                ∀ k, ∑ i, rate F tk E k i =
                  (s (k + 1) - s k) / Real.log (tk (k + 1) / tk k) := by
  obtain ⟨time, s₀, a₀, b₀, hclock, ha₀, ha₁, hb₀, hrate, ht₀, hsmall⟩ :=
    inverseClock_of_ricciWindows o h ρ t₀ hWindows
  refine ⟨time, s₀, a₀, b₀, hclock, ha₀, ha₁, hb₀, hrate, hsmall, ?_⟩
  intro hm hhm _
  obtain ⟨N, hN, hwindow⟩ := exists_window_length hhm ha₀
  refine ⟨N, hN, hwindow, ?_⟩
  intro M _
  let Q := sampledSpeed o h time hm
  obtain ⟨J, hJ⟩ := gridLayout_eventually Q N M hm hhm
  obtain ⟨Jclock, hJclock⟩ := (tendsto_atTop_atTop.1 (macroClock_tendsto hm hhm)) s₀
  let jLate := max J (Jclock + 2 * N + 1)
  have hlateJ : J ≤ jLate := le_max_left _ _
  have hlateClock : Jclock + 2 * N + 1 ≤ jLate := le_max_right _ _
  have hclockLate : s₀ ≤ macroClock hm (jLate - 2 * N) :=
    hJclock _ (by omega)
  refine ⟨jLate, by omega, hclockLate, ?_⟩
  intro j₀ hj₀
  let s := gridClock Q N M hm j₀
  let tk := fun k => time (s k)
  have hgrid : GridLayout Q N M hm j₀ := hJ j₀ (hlateJ.trans hj₀)
  have hsbase : s₀ ≤ s 0 := by
    change s₀ ≤ gridClock Q N M hm j₀ 0
    rw [gridClock_zero]
    exact hclockLate.trans ((macroClock_strictMono hm hhm).monotone (by omega))
  have hs : ∀ k, s₀ ≤ s k := fun k => hsbase.trans (hgrid.2.1.monotone (Nat.zero_le k))
  have htkpos : ∀ k, 0 < tk k := fun k => (hclock.2.2.1 (s k) (hs k)).1
  have htklate : ∀ k, t₀ ≤ tk k := fun k => ht₀ _ (hs k)
  have htkinc : ∀ k, tk k < tk (k + 1) := fun k =>
    hclock.2.1 (hs k) (hs (k + 1)) (hgrid.2.1 (Nat.lt_succ_self k))
  obtain ⟨E, hframes, htrace⟩ := singularFrames_of_shrinkingCharts hCharts tk htkpos htkinc htklate
  refine ⟨hgrid, fun k => ⟨hs k, htklate k⟩, E, hframes, ?_⟩
  intro k
  rw [htrace k, (hclock.2.2.1 (s (k + 1)) (hs (k + 1))).2,
    (hclock.2.2.1 (s k) (hs k)).2]

end Yau.Blueprint.Alignment.Y03Proof
