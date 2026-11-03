import Yau.Proofs.F01NativeTerminalChartLimit
import Yau.Proofs.F01SmoothHermitianChartLimit
import Mathlib.Topology.Order.IsLUB

/-! A genuine partial flow with the original quantitative comparison
has one constructed terminal smooth Hermitian field. Both the clock
sequence and every terminal chart are constructed in the proof. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Manifold Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem native_terminal_smooth_hermitian_field
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {ρ Tstar C : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρ1 : ρ ≤ 1)
    (hTstar : 0 ≤ Tstar) (hC : 1 ≤ C)
    (hEarly : ρ ^ 2 ≤ Tstar - (ρ * (1 / 4)) ^ 2 / 4)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (hU : ∀ T, 0 ≤ T → T < Tstar → SmoothSpaceTime U (Icc 0 T))
    (hU0 : ∀ x, U x 0 = 0)
    (hpot : ∀ s ∈ Ico 0 Tstar, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ T, 0 ≤ T → T < Tstar → ∀ x s, s ∈ Icc 0 T →
      HasDerivWithinAt (U x) (flowLogDetRatio g h x s) (Icc 0 T) s)
    (hflow : ∀ x s, s ∈ Ico 0 Tstar →
      (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) :
    ∃ τ : ℕ → ℝ, StrictMono τ ∧
      (∀ m, τ m ∈ Ioo (Tstar - (ρ * (1 / 4)) ^ 2 / 4) Tstar) ∧
      Tendsto τ atTop (𝓝 Tstar) ∧
      ∃ K : HermitianField M, MetricSmooth K ∧
        (∀ x, Tendsto (fun m => gMat (h (τ m)) x) atTop (𝓝 (gMat K x))) ∧
        (∀ x, (gMat K x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
          ((C : ℂ) • gMat g x - gMat K x).PosSemidef) ∧
        ∀ a q, TendstoUniformlyOn
          (fun m x => iteratedFDeriv ℝ q
            (fun z => pullbackMatrix (h (τ m)) (A.chart a) ((ρ * (1 / 4)) • z)) x)
          (iteratedFDeriv ℝ q (fun z => pullbackMatrix K (A.chart a) ((ρ * (1 / 4)) • z)))
          atTop (ball 0 (1 / 2)) := by
  let σ : ℝ := ρ * (1 / 4)
  have hσ : 0 < σ := mul_pos hρ (by norm_num)
  have hσr : σ ≤ A.radius := (show σ ≤ ρ by dsimp only [σ]; linarith [hρ.le]).trans hρr
  obtain ⟨τ, hMono, hτ, hLim⟩ := exists_seq_strictMono_tendsto'
    (show Tstar - σ ^ 2 / 4 < Tstar by nlinarith [sq_pos_of_pos hσ])
  have hMem (m : ℕ) : τ m ∈ Ico 0 Tstar :=
    ⟨(sq_nonneg ρ).trans (hEarly.trans (hτ m).1.le), (hτ m).2⟩
  have hLocal (a : M.Carrier) := native_terminal_chart_smooth_limit g hg A
    hρ hρr hρ1 hTstar hC hEarly h U hU hU0 hpot hpde hflow τ hτ hLim a
  obtain ⟨K, hSmooth, hNative, hOrders, hJets⟩ := smooth_hermitian_limit_of_chart_limits
    g hg A (fun m => h (τ m)) hσ hσr (inv_pos.mpr (show 0 < C by linarith))
    (fun m x => (hflow x (τ m) (hMem m)).1)
    (fun m x => (hflow x (τ m) (hMem m)).2) hLocal
  exact ⟨τ, hMono, hτ, hLim, K, hSmooth, hNative, hOrders, hJets⟩

end Yau.NodeProofs.F01Aux
