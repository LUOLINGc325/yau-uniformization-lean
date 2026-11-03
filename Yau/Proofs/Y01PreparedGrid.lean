import Yau.Proofs.Y01Parameters
import Yau.Proofs.Y01RunGluing
import Yau.Proofs.Y01GridModels

/-! The flag threshold and the first regular construction are chosen before
any later regular endpoint is requested. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment
open Yau.Blueprint.Alignment.Y04Proof

theorem exists_late_regular_endpoint
    {n : ℕ} {X : KahlerManifold n} {o : Pt X} {h : Flow X}
    {time : ℝ → ℝ} {s₀ a₀ b₀ hm M : ℝ} {N Dstar : ℕ}
    (hrate : ClockRateInput o h time s₀ a₀ b₀) (hhm : 0 < hm)
    (hN : 1 ≤ N) (hD : 1 ≤ Dstar) (hM : 0 < M) (hb₀ : 0 < b₀)
    (hpay : Real.log (Dstar : ℝ) + max 0 (Real.log (2 / b₀)) / (2 * N + 1 : ℝ) ≤
      M / (3 * (2 * N + 1 : ℝ))) (hgap : hm < M / (3 * (2 * N + 1 : ℝ)))
    (J : ℕ) : ∃ j : ℕ, J ≤ j ∧ Regular (sampledSpeed o h time hm) N M j := by
  obtain ⟨jBound, hbound, hdomain, hcharge⟩ :=
    exists_badCharging_bound hrate hhm hN hD hM hb₀ hpay hgap
  obtain ⟨j, hj, hreg⟩ := hcharge.2.2.2.2.2.1 J
  exact ⟨j, (le_max_left _ _).trans hj, hreg⟩

theorem prepared_original_grid
    (hY03 : Yau.BlueprintContracts.Y03_contract) (n Dstar : ℕ) (hD : 1 ≤ Dstar)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (r₀ r₁ σ C Cb t₀ : ℝ) (Φ : ℝ → ComplexVector n → Pt X)
    (F : ℝ → ℝ → ComplexVector n → ComplexVector n) (f : ℝ → Pt X → ComplexVector n)
    (hflow : FlowStage X o h U P ρ) (hwin : RicciWindows X o h ρ)
    (hjoint : JointPositiveClock X h) (hcharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f) :
    ∃ (time : ℝ → ℝ) (s₀ a₀ b₀ : ℝ), ClockParameter X o h ρ time s₀ ∧
      0 < a₀ ∧ a₀ < 1 ∧ 0 < b₀ ∧ ClockRateInput o h time s₀ a₀ b₀ ∧
      ∀ hm : ℝ, 0 < hm → hm < 1 → ∃ (N : ℕ) (M scale K eps b : ℝ),
        1 ≤ N ∧ Real.exp (-hm * N) ≤ a₀ ∧ 0 < M ∧
        Real.log (Dstar : ℝ) + max 0 (Real.log (2 / b₀)) / (2 * N + 1 : ℝ) ≤
          M / (3 * (2 * N + 1 : ℝ)) ∧ hm < M / (3 * (2 * N + 1 : ℝ)) ∧
        0 < scale ∧ 0 < K ∧ 0 < eps ∧ eps < 1 / (10 * (n + 1 : ℝ)) ∧ 0 < b ∧
        ∃ jLate : ℕ, N < jLate ∧
          ∀ J : ℕ, ∃ jBase : ℕ, max J jLate ≤ jBase ∧
            let Q := sampledSpeed o h time hm
            let s := gridClock Q N M hm jBase
            let tk := fun k => time (s k)
            Regular Q N M jBase ∧ GridLayout Q N M hm jBase ∧
              (∀ k, s₀ ≤ s k ∧ t₀ ≤ tk k) ∧
              ∃ (E : Frames n) (L : Changes n), SingularFrames F tk E ∧ RateOrder F tk E ∧
                (∀ k, ∑ i, rate F tk E k i =
                  (s (k + 1) - s k) / Real.log (tk (k + 1) / tk k)) ∧
                WindowRateBounds Q N M hm b₀ jBase (rate F tk E) ∧
                WeightEstimates Q N M hm scale K eps b jBase (rate F tk E) ∧
                ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ k, Regular Q N M (macroAt Q N M hm jBase k) →
                  ChangeAt (diagonal F tk E) (weight Q N M hm scale K eps jBase (rate F tk E))
                    (macroAt Q N M hm jBase) (macroClock hm) C c L k ∧
                  (Regular Q N M (macroAt Q N M hm jBase (k + 1)) →
                    JumpAt E (weight Q N M hm scale K eps jBase (rate F tk E)) L k) := by
  change Alignment.Y03 at hY03
  obtain ⟨time, s₀, a₀, b₀, hclock, ha₀, ha₁, hb₀, hrate, hwidth⟩ :=
    hY03 n X o h U P ρ r₀ r₁ σ C Cb t₀ Φ F f hflow hwin hjoint hcharts
  refine ⟨time, s₀, a₀, b₀, hclock, ha₀, ha₁, hb₀, hrate, ?_⟩
  intro hm hhm hhm1
  obtain ⟨N, hN, hwindow, hthreshold⟩ := hwidth hm hhm hhm1
  obtain ⟨M, hM, hpay, hgap⟩ := exists_flag_threshold Dstar N hm b₀
  obtain ⟨scale, K, eps, b, hscale, hK, heps, hepsSmall, hb,
    jLate, hjLate, hdomainLate, hgrids⟩ := hthreshold M hM
  refine ⟨N, M, scale, K, eps, b, hN, hwindow, hM, hpay, hgap,
    hscale, hK, heps, hepsSmall, hb, jLate, by omega, ?_⟩
  intro J
  obtain ⟨jBase, hbase, hreg⟩ := exists_late_regular_endpoint hrate hhm hN hD hM hb₀ hpay hgap (max J jLate)
  obtain ⟨hgrid, hdomain, E, hE, horder, htrace, hwindow, hweights, hruns⟩ :=
    hgrids jBase ((le_max_right _ _).trans hbase) hreg
  obtain ⟨L, C, c, hC, hc, hL⟩ := alignment_solution_from_runs hruns
  exact ⟨jBase, hbase, hreg, hgrid, hdomain, E, L, hE, horder, htrace, hwindow, hweights,
    C, c, hC, hc, hL⟩

end Yau.Proofs.Y01Aux
