import Yau.Proofs.F01PartialNativePotentialHolder
import Yau.Proofs.F01SpatialHolderEndpointLimit
import Yau.Proofs.F01SpaceTimeChart

/-! Actual native potential jets construct a smooth terminal scalar
in every bounded chart, with convergence of the complete spatial
derivative tower along the same terminal clock sequence. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Manifold Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem native_terminal_potential_chart_limit
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
    (hτlim : Tendsto τ atTop (𝓝 Tstar)) (a : M.Carrier) :
    ∃ W : Space n → ℝ, ContDiffOn ℝ ∞ W (ball 0 (1 / 2)) ∧
      ∀ k, TendstoUniformlyOn
        (fun m x => iteratedFDeriv ℝ k
          (fun z => (((ρ * (1 / 4)) ^ 2)⁻¹) * U ((A.chart a) ((ρ * (1 / 4)) • z)) (τ m)) x)
        (iteratedFDeriv ℝ k W) atTop (ball 0 (1 / 2)) := by
  let σ : ℝ := ρ * (1 / 4)
  let I : Set ℝ := Ioo (Tstar - σ ^ 2 / 4) Tstar
  have hσ : 0 < σ := mul_pos hρ (by norm_num)
  have hσr : σ ≤ A.radius := (show σ ≤ ρ by dsimp only [σ]; linarith [hρ.le]).trans hρr
  obtain ⟨B, _, hB⟩ := partial_native_potential_jet_holder g hg A hρ hρr hρ1 hTstar hC
    (α := 1 / 4) (β := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hEarly
  apply smooth_spatial_limit_of_parabolic_jet_holder
    (fun t z => (σ ^ 2)⁻¹ * U ((A.chart a) (σ • z)) t) (ball 0 (1 / 2)) I
    isOpen_ball (convex_ball _ _) (α := min (1 / 4) (1 / 4)) (by norm_num) B
    ?_ (fun k => hB h U hU hU0 hpot hpde hflow a k) τ hτ hτlim.cauchySeq
  intro t ht
  have htPos : 0 < t := (sq_pos_of_pos hρ).trans_le (hEarly.trans ht.1.le)
  have hChart := smoothSpaceTime_holomorphic_chart (hU t htPos.le ht.2)
    (A.chart a) (A.differentiable a)
  have hSlice : ContDiffOn ℝ ∞ (fun z => U ((A.chart a) z) t) (A.chart a).source :=
    hChart.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, htPos.le, le_rfl⟩)
  have hD : ContDiffOn ℝ ∞ (fun z : Space n => σ • z) (ball 0 (1 / 2)) :=
    (σ • ContinuousLinearMap.id ℝ (Space n)).contDiff.contDiffOn
  have hComp : ContDiffOn ℝ ∞ (fun z => U ((A.chart a) (σ • z)) t) (ball 0 (1 / 2)) :=
    hSlice.comp hD (fun z hz => A.closedBall_source a (ball_subset_closedBall
      (spatialDilation_mem_ball hσ hσr (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1) hz))))
  exact contDiffOn_const.mul hComp

end Yau.NodeProofs.F01Aux
