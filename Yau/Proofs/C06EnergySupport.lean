import Yau.Proofs.C06Integral
import Yau.Proofs.P07DistanceLeviSupport

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold
namespace Yau.Proofs.C06Aux
open Yau Yau.Blueprint Yau.NodeProofs Yau.NodeProofs.P07DistanceLevi
open Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract L19Aux
variable {n : ℕ}
set_option maxHeartbeats 1800000

/-- Actual squared-distance upper support with a strict radial complex direction. -/
theorem distanceSquare_strictUpperSupport (X : KahlerManifold n) (o q : Pt X) (hne : o ≠ q) :
    ∃ E : Pt X → ℝ, ∃ v : ComplexVector n,
      ContDiffAt ℝ 2 (inChart q E) (chartPt q q) ∧
      E q = inducedDistance X.metric.form o q ^ 2 ∧
      (∀ᶠ y in 𝓝 q, inducedDistance X.metric.form o y ^ 2 ≤ E y) ∧
      v ≠ 0 ∧
      leviDirection (leviC (inChart q E) (chartPt q q)) v <
        inducedDistance X.metric.form o q ^ 2 ∧
      fderiv ℝ (inChart q E) (chartPt q q) v =
        2 * inducedDistance X.metric.form o q ^ 2 := by
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
  let v : ComplexVector n := realTangentCoords (γ 1) (γ 1) (realCurveVelocity γ 1)
  let d : ℝ := inducedDistance X.metric.form o (γ 1)
  have hd : 0 < d := lt_of_le_of_ne (X.metric.induced_distance_nonneg _ _)
    (Ne.symm (fun h => hne (X.metric.induced_distance_eq_zero.mp h)))
  have hvv : realMetricInChart X.metric.form (γ 1) (chartPt (γ 1) (γ 1)) v v = d ^ 2 := by
    rw [realMetricInChart_tangentCoords X.metric.form (γ 1) (γ 1) (mem_chart_source _ _)]
    exact hspeed 1 (by norm_num)
  have hv : v ≠ 0 := by
    intro hz
    simp only [hz, map_zero, ContinuousLinearMap.zero_apply] at hvv
    nlinarith [sq_pos_of_pos hd]
  have hPv : (P 1) v = realCurveVelocity γ 1 := by
    change (P 1).toContinuousLinearMap v = _
    rw [hP1]
    exact realFrameCLM_realTangentCoords (γ 1) (γ 1) (mem_chart_source _ _) _
  have hDir : HasDerivAt (fun r : ℝ => Eu (r • v)) (2 * d ^ 2) 0 := by
    have hDensity (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
        HasDerivAt (fun r : ℝ => fieldPathSpeed X.metric.form
          (fun s => A s (r • v)) u ^ 2) (2 * d ^ 2) 0 := by
      have H := fieldPathSpeedSq_parallelVariation_hasDerivAt X.metric.form hh γ P A
        (Set.Ioo (-δ) (1+δ)) e.source isOpen_Ioo e.open_source hzero hGeoδ hA0 hP hFirst hA
        u (hunit hu) v
      have HC := geodesic_parallel_pairing_constant X.metric.form hh γ (fun s => P s v)
        (-δ) (1+δ) hGeoδ (fun c s hs hc => hP c s hs hc v)
        u 1 (hunit hu) h1
      rw [HC, hPv] at H
      change HasDerivAt _ (2 * actualSpeedSq X.metric.form γ 1) 0 at H
      rwa [hspeed 1 (by norm_num)] at H
    exact fieldPathEnergy_hasDerivAt_of_constant_density_firstVariation X.metric.form hh A e.source
      (Set.Ioo (-δ) (1+δ)) e.open_source isOpen_Ioo hzero hunit v (2 * d ^ 2) hDensity hA
  have hF : HasFDerivAt (inChart (γ 1) E)
      (fderiv ℝ (inChart (γ 1) E) (chartPt (γ 1) (γ 1))) (chartPt (γ 1) (e 0)) := by
    rw [he0]
    exact (hE.differentiableAt (by norm_num)).hasFDerivAt
  have hParam := hF.comp 0 hDe
  simp only [ContinuousLinearMap.comp_id] at hParam
  have hParam' : HasFDerivAt Eu
      (fderiv ℝ (inChart (γ 1) E) (chartPt (γ 1) (γ 1))) 0 :=
    hParam.congr_of_eventuallyEq
      (endpointEnergy_parameter_eventuallyEq_inChart (γ 1) E Eu e hzero he0 hEu)
  have hFirstValue : fderiv ℝ (inChart (γ 1) E) (chartPt (γ 1) (γ 1)) v = 2 * d ^ 2 := by
    have hP0 : HasFDerivAt Eu
        (fderiv ℝ (inChart (γ 1) E) (chartPt (γ 1) (γ 1))) ((0 : ℝ) • v) := by
      simpa only [zero_smul] using hParam'
    have H : HasDerivAt (fun r : ℝ => Eu (r • v))
        (fderiv ℝ (inChart (γ 1) E) (chartPt (γ 1) (γ 1)) v) 0 := by
      convert! hP0.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
      simp only [one_smul]
    exact H.unique hDir
  have hStrict : leviDirection (leviC (inChart (γ 1) E) (chartPt (γ 1) (γ 1))) v < d ^ 2 := by
    have Hbound := parallelVariation_paired_energySecond_lt X γ P A δ hδ e.source e.open_source
      hzero hGeoδ hA0 hP1 hPair hP hFirst hSecond d hd hspeed v hv hA
    change deriv (deriv (fun r : ℝ => Eu (r • v))) 0 +
      deriv (deriv (fun r : ℝ => Eu (r • (Complex.I • v)))) 0 < _ at Hbound
    rw [hCov, hCov, hvv] at Hbound
    rw [leviDirection_eq_paired_covariantHessian X.metric.form hh hk (γ 1)
      (z := chartPt (γ 1) (γ 1)) (mem_extChartAt_target (γ 1)) hE]
    linarith
  refine ⟨E, v, hE, hvalue, ?_, hv, hStrict, hFirstValue⟩
  have hy : γ 1 ∈ e.target := by rw [← he0]; exact e.map_source hzero
  filter_upwards [e.open_target.mem_nhds hy] with y hy
  exact hupper 0 (Set.mem_univ _) y hy

end Yau.Proofs.C06Aux
