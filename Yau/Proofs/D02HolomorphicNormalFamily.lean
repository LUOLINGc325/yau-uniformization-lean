import Yau.Proofs.D02LimitArea

/-! The same extraction now has a genuinely holomorphic normal limit on
the regular domain, finite actual area, and the original immersion bounds. -/

open scoped Topology Manifold ContDiff ENNReal CompactlySupported
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs

theorem discFamily_regular_holomorphic_subsequence {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {K : Set (Pt X)} (hK : IsCompact K) (A : ℝ) (fs : ℕ → ℂ → Pt X)
    (hfs : ∀ j, IsHolomorphicDisc (fs j) ∧
      (∀ z : ℂ, ‖z‖ = 1 → fs j z ∈ K) ∧ discArea X.metric.form (fs j) ≤ ENNReal.ofReal A) :
    letI := L12Aux.inducedMetricSpace X.metric
    ∃ (φ : ℕ → ℕ) (u : ℂ → ℝ) (μ : Measure ℂ) (f : ℂ → Pt X) (B_F B_u : ℝ),
      StrictMono φ ∧ 0 < B_F ∧ 0 < B_u ∧
      (∀ S : Set ℂ, IsCompact S → S ⊆ ball (0 : ℂ) 1 →
        IntegrableOn u S volume ∧ Tendsto
          (fun j => ∫ z in S, |immersionPotential X.metric.form F (fs (φ j) z) - u z|) atTop (𝓝 0)) ∧
      (∀ S : Set ℂ, IsCompact S → S ⊆ ball (0 : ℂ) 1 → μ S < ⊤) ∧
      μ (ball (0 : ℂ) 1)ᶜ = 0 ∧
      (∀ χ : ℂ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ ball (0 : ℂ) 1 →
        (2 * Real.pi) * (∫ z, χ z ∂μ) = ∫ z, u z * LeafCandidates.realPlanarLaplacian χ z) ∧
      IsOpen (regularPotentialDomain (ball (0 : ℂ) 1) μ) ∧
      IsPathConnected (regularPotentialDomain (ball (0 : ℂ) 1) μ) ∧
      ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ f (regularPotentialDomain (ball (0 : ℂ) 1) μ) ∧
      TendstoLocallyUniformlyOn (fun j => fs (φ j)) f atTop (regularPotentialDomain (ball (0 : ℂ) 1) μ) ∧
      (∫⁻ z in regularPotentialDomain (ball (0 : ℂ) 1) μ,
        ENNReal.ofReal (curveEnergyDensity X.metric.form f z)) ≤ ENNReal.ofReal A ∧
      (∫⁻ z in regularPotentialDomain (ball (0 : ℂ) 1) μ, ENNReal.ofReal
        (hermitianNormSq (X.metric.form (f z)) (physicalCurveDerivative f z))) < ⊤ ∧
      ∀ z ∈ regularPotentialDomain (ball (0 : ℂ) 1) μ,
        ‖F (f z)‖ ≤ B_F ∧ immersionDifferentialNormSq X.metric.form F (f z) ≤ B_u := by
  letI := L12Aux.inducedMetricSpace X.metric
  obtain ⟨B_F, B_u, _, hBF, hBu, _, hbound⟩ := uniformImmersionConstants X hF hImm hK
  obtain ⟨φ, u, μ, f₀, hφ, hlocal, hμ, hzero, hdist, _, ho, hpc, hcompact⟩ :=
    discFamily_regular_normal_subsequence X hF hImm hK A fs hfs
  let O := regularPotentialDomain (ball (0 : ℂ) 1) μ
  let f := domainLimitExtension f₀
  have hOD : O ⊆ ball (0 : ℂ) 1 := fun z hz => hz.1
  have hc : ContinuousOn f O := domainLimitExtension_continuousOn f₀
  have hconv : TendstoLocallyUniformlyOn (fun j => fs (φ j)) f atTop O :=
    domainLimitExtension_tendstoLocallyUniformly ho (fun j => fs (φ j)) f₀ hcompact
  have hfsO : ∀ j, ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ (fs (φ j)) O :=
    fun j => (hfs (φ j)).1.mono (hOD.trans ball_subset_closedBall)
  have hf := holomorphic_limit_contMDiffOn X.metric ho (fun j => fs (φ j)) f hfsO hc hconv
  refine ⟨φ, u, μ, f, B_F, B_u, hφ, hBF, hBu, hlocal, hμ, hzero, hdist, ho, hpc, hf, hconv,
    normal_limit_area_le X.metric ho hOD (fun j => fs (φ j)) f (fun j => (hfs (φ j)).1)
      hf hconv A (fun j => (hfs (φ j)).2.2),
    normal_limit_physical_energy_finite X.metric ho hOD (fun j => fs (φ j)) f
      (fun j => (hfs (φ j)).1) hf hconv A (fun j => (hfs (φ j)).2.2), ?_⟩
  have hnorm (j : ℕ) (z : ℂ) (hz : z ∈ O) :
      ‖F (fs (φ j) z)‖ ≤ B_F ∧ immersionDifferentialNormSq X.metric.form F (fs (φ j) z) ≤ B_u := by
    have hzD : ‖z‖ ≤ 1 := (show ‖z‖ < 1 from by
      simpa only [mem_ball, dist_zero_right] using hOD hz).le
    exact (hbound (fs (φ j)) (hfs (φ j)).1 (hfs (φ j)).2.1 z hzD).imp_right And.left
  have hFcont : Continuous (fun y => ‖F y‖) := hF.continuous.norm
  have hucont := L18Aux.continuous_of_smoothFn (immersionDifferentialNormSq_smooth X.metric.form
    (L12Aux.metricSmooth_of_smoothMetric X.metric) hF)
  exact fun z hz => ⟨normal_limit_continuous_bound X.metric (fun j => fs (φ j)) f hconv
    _ hFcont B_F (fun j z hz => (hnorm j z hz).1) z hz,
    normal_limit_continuous_bound X.metric (fun j => fs (φ j)) f hconv
      _ hucont B_u (fun j z hz => (hnorm j z hz).2) z hz⟩

end Yau.NodeProofs.D02Aux
