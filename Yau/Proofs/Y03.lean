import Yau.Proofs.Y03GeometricWeights
import Yau.Proofs.Y03UniformAlignment
import Yau.Proofs.Y03AdjacentBounds
import Yau.Proofs.Y03GridLower
import Yau.Proofs.Y03TimeScale

/-! The original geometric Y03 contract, on the actual inverse clock, grid and singular frames. -/

open scoped Topology
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

theorem y03 : Y03 := by
  intro n X o h U P ρ r₀ r₁ σ C Cb t₀ Φ F f hflow hWindows hjoint hCharts
  obtain ⟨time, s₀, a₀, b₀, hclock, ha₀, ha₁, hb₀, hrate, hsetup⟩ :=
    clock_grid_rateOrder_weights o h U P ρ hflow hWindows hjoint hCharts
  refine ⟨time, s₀, a₀, b₀, hclock, ha₀, ha₁, hb₀, hrate, ?_⟩
  intro hm hhm hhm'
  obtain ⟨N, hN, hwindow, hMsetup⟩ := hsetup hm hhm hhm'
  refine ⟨N, hN, hwindow, ?_⟩
  intro M hM
  obtain ⟨scale, K, eps, b, hscale, hK, heps, heps', hb, Jsetup, hJsetup, hssetup, hgrids⟩ := hMsetup M hM
  let Q := sampledSpeed o h time hm
  obtain ⟨Lclock, hLclock⟩ := (tendsto_atTop_atTop.1 (macroClock_tendsto hm hhm)) s₀
  have hsL := hLclock Lclock le_rfl
  obtain ⟨cQ, hcQ, hQlower⟩ := sampledSpeed_lower_late hrate hhm hsL
  have hQmono := sampledSpeed_monotone_late hrate hhm hsL
  have hn : 0 < n := dimension_pos_of_clockRateInput hrate
  let B := b⁻¹ * Real.exp M
  have hB : 0 < B := mul_pos (inv_pos.2 hb) (Real.exp_pos _)
  let γ := (1 / 2 : ℝ) / ((n : ℝ) * B)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hγ : 0 < γ := div_pos (by norm_num) (mul_pos hnR hB)
  obtain ⟨Jalign, halign⟩ := uniform_alignment_runs (n := n) hhm heps hB hγ
  obtain ⟨Jgrid, hgridLower⟩ := uniform_grid_macro_lower Q N M hhm
  let jLate := max Jsetup (max Jalign (max Jgrid (Lclock + N + 1)))
  have hlateSetup : Jsetup ≤ jLate := le_max_left _ _
  have hlateAlign : Jalign ≤ jLate := (le_max_left _ _).trans (le_max_right _ _)
  have hlateGrid : Jgrid ≤ jLate := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hlateClock : Lclock + N + 1 ≤ jLate :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hlateN : 2 * N < jLate := hJsetup.trans_le hlateSetup
  have hsLate : s₀ ≤ macroClock hm (jLate - 2 * N) :=
    hssetup.trans ((macroClock_strictMono hm hhm).monotone (Nat.sub_le_sub_right hlateSetup (2 * N)))
  refine ⟨scale, K, eps, b, hscale, hK, heps, heps', hb, jLate, hlateN, hsLate, ?_⟩
  intro j₀ hj₀ hreg₀
  obtain ⟨hgrid, hdomain, E, hE, horder, htrace, hwindowBounds, hweights⟩ :=
    hgrids j₀ (hlateSetup.trans hj₀) hreg₀
  let s := gridClock Q N M hm j₀
  let tk := fun k => time (s k)
  refine ⟨hgrid, hdomain, E, hE, horder, htrace, hwindowBounds, hweights, ?_⟩
  apply halign Q N M scale K b j₀ (hlateAlign.trans hj₀) F tk E hE horder hweights
  intro k hreg hreg'
  let j := macroAt Q N M hm j₀ k
  have hj : Lclock + N + 1 ≤ j := hlateClock.trans (hj₀.trans (macroAt_mem Q N M hm j₀ k).1)
  have hbounds := adjacent_regular_rate_bounds Q N Lclock M hm scale K eps b cQ hM.le hb hcQ j₀
    (by omega) hQmono hQlower hE hweights k hreg hreg'
  have hq : 0 < Q j := hcQ.trans_le (hQlower j (by omega))
  refine ⟨hq, hbounds.1, hbounds.2, ?_⟩
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hstep : (1 / 2 : ℝ) * Real.sqrt (macroClock hm j) ≤ s (k + 1) - s k := by
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hgridLower j₀ (hlateGrid.trans hj₀) k
  have htime := trace_time_scale (μ := rate F tk E k) (q := Q j) (B := B) (ch := (1 / 2 : ℝ))
    (T := Real.log (tk (k + 1) / tk k)) (Δ := s (k + 1) - s k) (S := macroClock hm j) (j := (j : ℝ))
    hn hB (log_time_ratio_pos (hE k).1 (hE k).2.1) hjpos (fun i => (hbounds.1 i).2) (htrace k) hstep
  simpa only [γ, theta] using htime

end Yau.Blueprint.Alignment.Y03Proof
