import Yau.Proofs.F01PartialNativeMatrixHolder
import Yau.Proofs.F01SpatialHolderEndpointLimit
import Yau.Proofs.F01PotentialMetricSmooth
import Yau.Proofs.F01ChartGramSmooth

/-! The original partial-flow identities and quantitative native
estimates construct smooth terminal chart matrices. No terminal metric,
terminal potential or continuation is among the hypotheses. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Manifold Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem native_terminal_chart_smooth_limit
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
    ∃ G : Space n → Matrix (Fin n) (Fin n) ℂ,
      ContDiffOn ℝ ∞ G (ball 0 (1 / 2)) ∧
      ∀ k, TendstoUniformlyOn
        (fun m x => iteratedFDeriv ℝ k
          (fun z => pullbackMatrix (h (τ m)) (A.chart a) ((ρ * (1 / 4)) • z)) x)
        (iteratedFDeriv ℝ k G) atTop (ball 0 (1 / 2)) := by
  let σ : ℝ := ρ * (1 / 4)
  let I : Set ℝ := Ioo (Tstar - σ ^ 2 / 4) Tstar
  have hσ : 0 < σ := mul_pos hρ (by norm_num)
  have hσr : σ ≤ A.radius := (show σ ≤ ρ by dsimp only [σ]; linarith [hρ.le]).trans hρr
  obtain ⟨B, _, hB⟩ := partial_native_matrix_jet_holder g hg A hρ hρr hρ1 hTstar hC
    (α := 1 / 4) (β := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hEarly
  apply smooth_spatial_limit_of_parabolic_jet_holder
    (fun t z => pullbackMatrix (h t) (A.chart a) (σ • z)) (ball 0 (1 / 2)) I
    isOpen_ball (convex_ball _ _) (α := min (1 / 4) (1 / 4)) (by norm_num) B
    ?_ (fun k => hB h U hU hU0 hpot hpde hflow a k) τ hτ hτlim.cauchySeq
  intro t ht
  have htPos : 0 < t := (sq_pos_of_pos hρ).trans_le (hEarly.trans ht.1.le)
  have hSub : Icc 0 t ⊆ Ico 0 Tstar := fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  have hFamily := metricFamilySmooth_of_potential_identity g hg h U
    (uniqueDiffOn_Icc htPos) (hU t htPos.le ht.2)
    (fun s hs x => hpot s (hSub hs) x)
  have htMetric : MetricSmooth (h t) := metricFamilySmooth_slice hFamily ⟨htPos.le, le_rfl⟩
  have hf : ContDiffOn ℝ ∞ (fun w => pullbackMatrix (h t) (A.chart a) w)
      (ball 0 A.radius) := matrix_contDiffOn_of_entries (fun i j =>
    (pullbackMatrix_entry_contDiffOn (h t) htMetric (A.chart a) (A.differentiable a) i j).mono
      (ball_subset_closedBall.trans (A.closedBall_source a)))
  have hD : ContDiffOn ℝ ∞ (fun z : Space n => σ • z) (ball 0 (1 / 2)) :=
    (σ • ContinuousLinearMap.id ℝ (Space n)).contDiff.contDiffOn
  exact hf.comp hD (fun z hz => spatialDilation_mem_ball hσ hσr
    (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1) hz))

end Yau.NodeProofs.F01Aux
