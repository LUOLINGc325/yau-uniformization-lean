import Yau.Proofs.F01NativeTerminalPotentialChart
import Yau.Proofs.F01SmoothScalarChartLimit

/-! The same terminal clock sequence constructs one genuine native
smooth potential, with all bounded-chart spatial jet limits. No
terminal scalar representative is supplied. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Manifold Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem native_terminal_smooth_potential
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
      ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef)
    (τ : ℕ → ℝ)
    (hτ : ∀ m, τ m ∈ Ioo (Tstar - (ρ * (1 / 4)) ^ 2 / 4) Tstar)
    (hτlim : Tendsto τ atTop (𝓝 Tstar)) :
    ∃ u : M.Carrier → ℝ, SmoothFn u ∧
      (∀ x, Tendsto (fun m => U x (τ m)) atTop (𝓝 (u x))) ∧
      ∀ a q, TendstoUniformlyOn
        (fun m x => iteratedFDeriv ℝ q
          (fun z => (((ρ * (1 / 4)) ^ 2)⁻¹) * U ((A.chart a) ((ρ * (1 / 4)) • z)) (τ m)) x)
        (iteratedFDeriv ℝ q
          (fun z => (((ρ * (1 / 4)) ^ 2)⁻¹) * u ((A.chart a) ((ρ * (1 / 4)) • z))))
        atTop (ball 0 (1 / 2)) := by
  have hσ : 0 < ρ * (1 / 4) := mul_pos hρ (by norm_num)
  have hσr : ρ * (1 / 4) ≤ A.radius :=
    (show ρ * (1 / 4) ≤ ρ by linarith [hρ.le]).trans hρr
  apply smooth_scalar_limit_of_chart_limits g hg A (fun m x => U x (τ m)) hσ hσr
  intro a
  exact native_terminal_potential_chart_limit g hg A hρ hρr hρ1 hTstar hC hEarly
    h U hU hU0 hpot hpde hflow τ hτ hτlim a

end Yau.NodeProofs.F01Aux
