import Yau.Proofs.Y01PreparedGrid

/-! The original positive-clock rate identity handles the literal n=0
branch without adding a positive-dimension restriction to Y01. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment

theorem original_Y03_zero_dimension_impossible
    (hY03 : Yau.BlueprintContracts.Y03_contract)
    (X : KahlerManifold 0) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (r₀ r₁ σ C Cb t₀ : ℝ) (Φ : ℝ → ComplexVector 0 → Pt X)
    (F : ℝ → ℝ → ComplexVector 0 → ComplexVector 0) (f : ℝ → Pt X → ComplexVector 0)
    (hflow : FlowStage X o h U P ρ) (hwin : RicciWindows X o h ρ)
    (hjoint : JointPositiveClock X h) (hcharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f) : False := by
  obtain ⟨time, s₀, a₀, b₀, hclock, ha₀, ha₁, hb₀, hrate, hwidth⟩ :=
    prepared_original_grid hY03 0 1 le_rfl X o h U P ρ r₀ r₁ σ C Cb t₀ Φ F f
      hflow hwin hjoint hcharts
  obtain ⟨N, M, scale, K, eps, b, hN, hwindow, hM, hpay, hgap,
    hscale, hK, heps, hepsSmall, hb, jLate, hjLate, hbase⟩ :=
    hwidth (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨jBase, hjBase, hreg, hgrid, hdomain, E, L, hE, horder, htrace,
    hwindow', hweights, C', c', hC', hc', hL⟩ := hbase 0
  exact zero_dimension_grid_rates_impossible hgrid hE htrace

end Yau.Proofs.Y01Aux
