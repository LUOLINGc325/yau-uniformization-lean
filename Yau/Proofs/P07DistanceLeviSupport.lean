import Yau.Proofs.P07DistanceLeviMinimizer
import Yau.Proofs.P07DistanceLeviComparison
import Yau.Proofs.P07DistanceLeviChart
import Yau.LeafProofs.L23LocalDistanceSupportEnergyGradient
import Yau.LeafProofs.L23LocalDistanceSupportEnergyLaplacianTraceRegularity
import Yau.LeafProofs.L23LocalDistanceSupportEnergyMajorant

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P07DistanceLevi
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract L19Aux

variable {n : ℕ}
set_option maxHeartbeats 1800000

/-- A genuine energy upper support of the distance square, with both
complex-direction estimates. The input is exactly the original manifold. -/
theorem distanceSquare_centeredUpperSupport (X : KahlerManifold n) (o q : Pt X) :
    ∃ E : Pt X → ℝ,
      ContDiffAt ℝ 2 (inChart q E) (chartPt q q) ∧
      E q = inducedDistance X.metric.form o q ^ 2 ∧
      (∀ᶠ y in 𝓝 q, inducedDistance X.metric.form o y ^ 2 ≤ E y) ∧
      (∀ v : ComplexVector n, leviDirection (leviC (inChart q E) (chartPt q q)) v ≤
        2 * leviDirection (gMat X.metric.form q) v) ∧
      (∀ v : ComplexVector n, directionalRankOne (inChart q E) (chartPt q q) v ≤
        (4 * inducedDistance X.metric.form o q ^ 2) * leviDirection (gMat X.metric.form q) v) := by
  letI := manifold_realSmooth X.manifold
  have hh := metricSmooth_of_smoothMetric X.metric
  have hk : KahlerClosed X.metric.form := X.kahler_metric
  obtain ⟨ε,hε,γ,hγ0,hγ1,hGeo,hspeed⟩ := exists_complete_minimizing_fieldGeodesic X.metric o q
  subst q
  obtain ⟨δ,e,P,A,hδ,hδε,hzero,he0,hA,hinv,hA0,hend,hP1,hPair,hJets⟩ :=
    parallelEndpointVariation n X.manifold X.metric.form hh Set.univ isOpen_univ γ ε hε
      hGeo (fun _ _ => Set.mem_univ _)
  have hsub : Set.Ioo (-δ) (1+δ) ⊆ Set.Ioo (-ε) (1+ε) := by
    intro u hu
    constructor <;> linarith [hu.1,hu.2]
  have hGeoδ : FieldGeodesicOn X.metric.form γ (Set.Ioo (-δ) (1+δ)) :=
    ⟨hGeo.1.mono hsub,fun c u hu hc => hGeo.2 c u (hsub hu) hc⟩
  have hunit : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-δ) (1+δ) := by
    intro u hu
    constructor <;> linarith [hu.1,hu.2]
  have h1 : (1 : ℝ) ∈ Set.Ioo (-δ) (1+δ) := hunit (by norm_num)
  have hP (c : Pt X) (u : ℝ) (hu : u ∈ Set.Ioo (-δ) (1+δ))
      (hc : γ u ∈ (chartAt (ComplexVector n) c).source) :=
    (hJets c u hu (by simpa only [extChartAt_source] using hc)).1
  have hFirst (c : Pt X) (u : ℝ) (hu : u ∈ Set.Ioo (-δ) (1+δ))
      (hc : γ u ∈ (chartAt (ComplexVector n) c).source) :=
    (hJets c u hu (by simpa only [extChartAt_source] using hc)).2.1
  have hSecond (c : Pt X) (u : ℝ) (hu : u ∈ Set.Ioo (-δ) (1+δ))
      (hc : γ u ∈ (chartAt (ComplexVector n) c).source) :=
    (hJets c u hu (by simpa only [extChartAt_source] using hc)).2.2
  let E : Pt X → ℝ := fun z => fieldPathEnergy X.metric.form (fun u => A u (e.symm z))
  let Eu : ComplexVector n → ℝ := fun v => fieldPathEnergy X.metric.form (fun u => A u v)
  have hEu : Set.EqOn Eu (fun v => E (e v)) e.source := by
    intro v hv
    dsimp only [Eu,E]
    rw [e.left_inv hv]
  have hE := (endpointVariation_staticEnergy_contDiffAt_two X.metric.form hh (γ 1)
    e A δ hδ hzero he0 hA hinv).2
  have Hfam : MetricFamilySmooth (fun _ : ℝ => X.metric.form) Set.univ := by
    intro c i j
    exact (hh c i j).comp contDiffOn_fst (fun p hp => hp.1)
  obtain ⟨_,hvalue,hupper⟩ := endpointVariation_energy_majorant (fun _ : ℝ => X.metric.form)
    Set.univ isOpen_univ Hfam o (γ 1) 0 (Set.mem_univ _) e A γ δ hδ rfl hzero he0 hA0
    (fun v hv => ⟨(hend v hv).1.trans hγ0,(hend v hv).2.1⟩) hspeed hA hinv
      (hGeoδ.1.of_le (by norm_num))
  have hgrad := realGradPair_endpointVariation_fieldPathEnergy X.metric.form hh γ P e A δ hδ hGeoδ
    hzero he0 hA0 (fun v hv => (hend v hv).2.1) hP1 hP hFirst hA hinv
  rw [hspeed 1 (by norm_num)] at hgrad
  have hF1 : HasFDerivAt (fun v => chartPt (γ 1) (A 1 v))
      ((realTangentCoords (γ 1) (γ 1)).comp (P 1).toContinuousLinearMap) 0 := by
    simpa only [one_smul] using hFirst (γ 1) 1 h1 (mem_chart_source _ _)
  have hDe := endpointChart_hasFDerivAt_id (γ 1) e (fun v => A 1 v) hzero
    (P 1).toContinuousLinearMap hP1 (fun v hv => (hend v hv).2.1) hF1
  have hS1 (w : ComplexVector n) : HasDerivAt (deriv (fun s : ℝ => chartPt (γ 1) (A 1 (s • w))))
      (-chartChristoffelBilin X.metric.form (γ 1) (chartPt (γ 1) (γ 1))
        (realTangentCoords (γ 1) (γ 1) ((P 1).toContinuousLinearMap w))
        (realTangentCoords (γ 1) (γ 1) ((P 1).toContinuousLinearMap w))) 0 := by
    simpa only [one_smul,ContinuousLinearEquiv.coe_coe] using hSecond (γ 1) 1 h1 (mem_chart_source _ _) w
  have hEndpoint := endpointChart_contDiffAt_three_of_terminalVariation (γ 1) e A δ hδ hzero he0
    (fun v hv => (hend v hv).2.1) hA
  have hCov (w : ComplexVector n) : deriv (deriv (fun r : ℝ => Eu (r • w))) 0 =
      chartCovHessianBilin X.metric.form (γ 1) (inChart (γ 1) E) (chartPt (γ 1) (γ 1)) w w := by
    rw [endpointEnergy_ray_secondDeriv_eq_inChart (γ 1) E Eu e hzero he0 hEu w]
    have hEndpoint' : ContDiffAt ℝ 2 (fun v => chartPt (γ 1) (e v)) ((0 : ℝ) • w) := by
      simpa only [zero_smul] using hEndpoint.of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)
    have hc₂ : ContDiffAt ℝ 2 (fun r : ℝ => chartPt (γ 1) (e (r • w))) 0 :=
      hEndpoint'.comp (f := fun r : ℝ => r • w)
        (g := fun v : ComplexVector n => chartPt (γ 1) (e v)) 0
        (contDiffAt_id.smul contDiffAt_const)
    apply scalar_normalRay_secondDeriv X.metric.form (γ 1) (inChart (γ 1) E)
      (fun r : ℝ => chartPt (γ 1) (e (r • w))) ?_ hE
      hc₂ w
      (endpointRay_hasDerivAt (γ 1) e hDe w)
      (endpointRay_secondJet_of_terminalVariation X.metric.form (γ 1) e (fun v => A 1 v)
        hzero (P 1).toContinuousLinearMap hP1 (fun v hv => (hend v hv).2.1) hS1 w)
    simp only [zero_smul,he0]
  refine ⟨E,hE,hvalue,?_,?_,?_⟩
  · have hy : γ 1 ∈ e.target := by rw [← he0]; exact e.map_source hzero
    filter_upwards [e.open_target.mem_nhds hy] with y hy
    exact hupper 0 (Set.mem_univ _) y hy
  · intro v
    have Hbound := rayEnergy_paired_secondDeriv_le_of_density_bound X.metric.form hh A
      (Set.Ioo (-δ) (1+δ)) e.source isOpen_Ioo e.open_source hunit hzero v
      (4 * realMetricInChart X.metric.form (γ 1) (chartPt (γ 1) (γ 1)) v v)
      (fun u hu => parallelVariation_paired_secondDensity_le X γ P A δ hδ e.source e.open_source
        hzero hGeoδ hA0 hP1 hPair hP hFirst hSecond u (hunit hu) v hA) hA
    change deriv (deriv (fun r : ℝ => Eu (r • v))) 0 +
      deriv (deriv (fun r : ℝ => Eu (r • (Complex.I • v)))) 0 ≤ _ at Hbound
    have hMetric : realMetricInChart X.metric.form (γ 1) (chartPt (γ 1) (γ 1)) v v =
        2 * leviDirection (hMat X.metric.form (γ 1) (chartPt (γ 1) (γ 1))) v :=
      realMetricInChart_eq_twice_leviDirection X.metric.form (γ 1)
        (z := chartPt (γ 1) (γ 1)) (mem_extChartAt_target (γ 1)) v
    rw [hCov,hCov,hMetric] at Hbound
    rw [leviDirection_eq_paired_covariantHessian X.metric.form hh hk (γ 1)
      (z := chartPt (γ 1) (γ 1)) (mem_extChartAt_target (γ 1)) hE]
    change _ ≤ 2 * leviDirection (hMat X.metric.form (γ 1) (chartPt (γ 1) (γ 1))) v
    linarith
  · intro v
    have H := directionalRankOne_le_chartGradientPair X.metric.form (γ 1) (inChart (γ 1) E)
      (mem_extChartAt_target (γ 1)) v
    change directionalRankOne (inChart (γ 1) E) (chartPt (γ 1) (γ 1)) v ≤
      realGradPair X.metric.form E E (γ 1) * leviDirection (gMat X.metric.form (γ 1)) v at H
    rwa [hgrad] at H

/-- The support is produced in the arbitrary original chart required by
the compact-test weak Levi definition, including cut points. -/
theorem distanceSquare_upperSupport_inChart (X : KahlerManifold n) (o c : Pt X)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    ∃ S : ComplexVector n → ℝ,
      ContDiffAt ℝ 2 S z ∧
      S z = (distFrom X.metric.form o (chartInv c z)) ^ 2 ∧
      (∀ᶠ w in 𝓝 z, (distFrom X.metric.form o (chartInv c w)) ^ 2 ≤ S w) ∧
      (∀ v : ComplexVector n, leviDirection (leviC S z) v ≤
        2 * leviDirection (hMat X.metric.form c z) v) ∧
      (∀ v : ComplexVector n, directionalRankOne S z v ≤
        (4 * (distFrom X.metric.form o (chartInv c z)) ^ 2) *
          leviDirection (hMat X.metric.form c z) v) := by
  let q := chartInv c z
  obtain ⟨E,hE,hvalue,hupper,hLevi,hRank⟩ := distanceSquare_centeredUpperSupport X o q
  have hq : chartInv c z ∈ (extChartAt (ComplexModel n) q).source := mem_extChartAt_source q
  have H := inChart_directional_bounds_transport X.metric.form E c q hz hq hE
    2 (4 * inducedDistance X.metric.form o q ^ 2) hLevi hRank
  refine ⟨inChart c E,H.1,hvalue,?_,H.2.1,H.2.2⟩
  exact (continuousAt_extChartAt_symm'' hz).eventually hupper

end Yau.NodeProofs.P07DistanceLevi
