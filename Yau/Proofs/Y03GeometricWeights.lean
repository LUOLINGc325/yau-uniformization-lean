import Yau.Proofs.Y03Setup
import Yau.Proofs.Y03RateOrder
import Yau.Proofs.Y03WindowRates
import Yau.Proofs.Y03WeightConstants

/-! The complete geometric clock, rates and propagated weights on one uniform set of witnesses. -/

open scoped Topology
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

theorem clock_grid_rateOrder_weights {n : ℕ} {X : KahlerManifold n}
    (o : Pt X) (h : Flow X) (U P ρ : STF X) {r₀ r₁ σ C Cb t₀ : ℝ}
    {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n}
    (hflow : FlowStage X o h U P ρ) (hWindows : RicciWindows X o h ρ)
    (hjoint : JointPositiveClock X h)
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f) :
    ∃ (time : ℝ → ℝ) (s₀ a₀ b₀ : ℝ), ClockParameter X o h ρ time s₀ ∧
      0 < a₀ ∧ a₀ < 1 ∧ 0 < b₀ ∧ ClockRateInput o h time s₀ a₀ b₀ ∧
      ∀ hm, 0 < hm → hm < 1 → ∃ N : ℕ, 1 ≤ N ∧ Real.exp (-hm * N) ≤ a₀ ∧
        ∀ M : ℝ, 0 < M → ∃ scale K eps b : ℝ, 0 < scale ∧ 0 < K ∧ 0 < eps ∧
          eps < 1 / (10 * (n + 1 : ℝ)) ∧ 0 < b ∧ ∃ jLate : ℕ, 2 * N < jLate ∧
          s₀ ≤ macroClock hm (jLate - 2 * N) ∧
          ∀ j₀, jLate ≤ j₀ → Regular (sampledSpeed o h time hm) N M j₀ →
            let Q := sampledSpeed o h time hm
            let s := gridClock Q N M hm j₀
            let tk := fun k => time (s k)
            GridLayout Q N M hm j₀ ∧ (∀ k, s₀ ≤ s k ∧ t₀ ≤ tk k) ∧
            ∃ E : Frames n, SingularFrames F tk E ∧ RateOrder F tk E ∧
              (∀ k, ∑ i, rate F tk E k i =
                (s (k + 1) - s k) / Real.log (tk (k + 1) / tk k)) ∧
              WindowRateBounds Q N M hm b₀ j₀ (rate F tk E) ∧
              WeightEstimates Q N M hm scale K eps b j₀ (rate F tk E) := by
  obtain ⟨time, s₀, a₀, b₀, hclock, ha₀, ha₁, hb₀, hrate, _, hsetup⟩ :=
    clock_grid_singularFrames o h ρ hWindows hCharts
  refine ⟨time, s₀, a₀, b₀, hclock, ha₀, ha₁, hb₀, hrate, ?_⟩
  intro hm hhm hhm'
  obtain ⟨N, hN, hwindow, hMsetup⟩ := hsetup hm hhm hhm'
  refine ⟨N, hN, hwindow, ?_⟩
  intro M hM
  let Q := sampledSpeed o h time hm
  obtain ⟨Jsetup, hJsetup, hssetup, hgrids⟩ := hMsetup M hM
  obtain ⟨L, hL⟩ := (tendsto_atTop_atTop.1 (macroClock_tendsto hm hhm)) s₀
  have hsL := hL L le_rfl
  obtain ⟨c, hc, hQlower⟩ := sampledSpeed_lower_late hrate hhm hsL
  have hQmono := sampledSpeed_monotone_late hrate hhm hsL
  obtain ⟨scale, K, eps, b, hscale, hK, heps, heps', hb, Jweights, hweights⟩ :=
    weightEstimates_uniform_constants Q N M hm b₀ c hM hhm hb₀ hc L hQmono hQlower
  obtain ⟨T, hwin⟩ := windowRateBounds_of_geometric_clock hflow hjoint hCharts hWindows M
    hclock hrate ha₀ hb₀ hhm hwindow
  obtain ⟨JT, hJT⟩ := (tendsto_atTop_atTop.1 (hclock.2.2.2.comp (macroClock_tendsto hm hhm))) T
  let jLate := max Jsetup (max Jweights JT)
  have hlateSetup : Jsetup ≤ jLate := le_max_left _ _
  have hlateWeights : Jweights ≤ jLate := (le_max_left _ _).trans (le_max_right _ _)
  have hlateT : JT ≤ jLate := (le_max_right _ _).trans (le_max_right _ _)
  have hlateN : 2 * N < jLate := hJsetup.trans_le hlateSetup
  have hlateClock : s₀ ≤ macroClock hm (jLate - 2 * N) :=
    hssetup.trans ((macroClock_strictMono hm hhm).monotone
      (Nat.sub_le_sub_right hlateSetup (2 * N)))
  refine ⟨scale, K, eps, b, hscale, hK, heps, heps', hb, jLate, hlateN, hlateClock, ?_⟩
  intro j₀ hj₀ _
  obtain ⟨hgrid, hdomain, E, hE, htrace⟩ := hgrids j₀ (hlateSetup.trans hj₀)
  let s := gridClock Q N M hm j₀
  let tk := fun k => time (s k)
  have horder : RateOrder F tk E :=
    rateOrder_of_jointPositiveClock hflow hjoint hCharts hE (fun k => (hdomain k).2)
  have hsleft : s₀ ≤ macroClock hm (j₀ - N) :=
    hlateClock.trans ((macroClock_strictMono hm hhm).monotone (by omega))
  have hwindowBounds : WindowRateBounds Q N M hm b₀ j₀ (rate F tk E) :=
    hwin j₀ (by omega) hsleft (hJT j₀ (hlateT.trans hj₀)) E hE (fun k => (hdomain k).2)
  exact ⟨hgrid, hdomain, E, hE, horder, htrace, hwindowBounds,
    hweights j₀ (hlateWeights.trans hj₀) (rate F tk E) horder.2 hwindowBounds⟩

end Yau.Blueprint.Alignment.Y03Proof
