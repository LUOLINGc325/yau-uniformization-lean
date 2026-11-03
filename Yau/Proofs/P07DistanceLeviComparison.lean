import Yau.Proofs.P07DistanceLeviCurvature
import Yau.Proofs.P07DistanceLeviRankOne
import Yau.LeafProofs.L23DistanceEnergyParallelSecond
import Yau.LeafProofs.L23DistanceEnergyRayIntegral

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P07DistanceLevi
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract

variable {n : ℕ}

theorem rayEnergy_paired_secondDeriv_le_of_density_bound
    {M : ComplexManifold n} (h : HermitianField M) (hh : MetricSmooth h)
    (A : ℝ → ComplexVector n → M.Carrier) (J : Set ℝ) (U : Set (ComplexVector n))
    (hJ : IsOpen J) (hU : IsOpen U) (hunit : Set.Icc (0 : ℝ) 1 ⊆ J)
    (hzero : (0 : ComplexVector n) ∈ U) (v : ComplexVector n) (B : ℝ)
    (hbound : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      deriv (deriv (fun r : ℝ => fieldPathSpeed h (fun s => A s (r • v)) u ^ 2)) 0 +
        deriv (deriv (fun r : ℝ => fieldPathSpeed h
          (fun s => A s (r • (Complex.I • v))) u ^ 2)) 0 ≤ B) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ U) →
    deriv (deriv (fun r : ℝ => fieldPathEnergy h (fun s => A s (r • v)))) 0 +
      deriv (deriv (fun r : ℝ => fieldPathEnergy h (fun s => A s (r • (Complex.I • v))))) 0 ≤ B := by
  letI := manifold_realSmooth M
  intro hA
  have hv := rayEnergy_secondDensity_integrableOn h hh A J U hJ hU hunit hzero v hA
  have hIv := rayEnergy_secondDensity_integrableOn h hh A J U hJ hU hunit hzero
    (Complex.I • v) hA
  rw [rayEnergy_secondDeriv_eq_integral h hh A J U hJ hU hunit hzero v hA,
    rayEnergy_secondDeriv_eq_integral h hh A J U hJ hU hunit hzero (Complex.I • v) hA,
    ← integral_add hv hIv]
  have H : (∫ u in Set.Icc (0 : ℝ) 1,
      deriv (deriv (fun r : ℝ => fieldPathSpeed h (fun s => A s (r • v)) u ^ 2)) 0 +
        deriv (deriv (fun r : ℝ => fieldPathSpeed h
          (fun s => A s (r • (Complex.I • v))) u ^ 2)) 0) ≤
      ∫ _u in Set.Icc (0 : ℝ) 1, B := by
    apply integral_mono_ae (hv.add hIv) (integrableOn_const (hs := by simp))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact hbound u hu
  simpa [integral_const, Measure.real] using H

theorem parallelVariation_paired_secondDensity_le
    (X : KahlerManifold n) (γ : ℝ → Pt X)
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (A : ℝ → ComplexVector n → Pt X) (δ : ℝ) (hδ : 0 < δ)
    (U : Set (ComplexVector n)) (hU : IsOpen U) (hzero : (0 : ComplexVector n) ∈ U)
    (hγ : FieldGeodesicOn X.metric.form γ (Set.Ioo (-δ) (1+δ)))
    (hA0 : ∀ u ∈ Set.Ioo (-δ) (1+δ), A u 0 = γ u)
    (hP1 : (P 1).toContinuousLinearMap = realFrameCLM (γ 1) (γ 1))
    (hPair : ∀ u ∈ Set.Ioo (-δ) (1+δ), ∀ v w : ComplexVector n,
      (underlyingRealRiemannianMetric X.metric.form).inner (γ u) (P u v) (P u w) =
        realMetricInChart X.metric.form (γ 1) (chartPt (γ 1) (γ 1)) v w)
    (hP : ∀ (c : Pt X) (u : ℝ), u ∈ Set.Ioo (-δ) (1+δ) →
      γ u ∈ (chartAt (ComplexVector n) c).source → ∀ w : ComplexVector n,
      HasDerivAt (fun s => realTangentCoords c (γ s) (P s w))
        (-chartChristoffelBilin X.metric.form c (chartPt c (γ u)) (geoChartState γ c u).2
          (realTangentCoords c (γ u) (P u w))) u)
    (hFirst : ∀ (c : Pt X) (u : ℝ), u ∈ Set.Ioo (-δ) (1+δ) →
      γ u ∈ (chartAt (ComplexVector n) c).source →
      HasFDerivAt (fun v => chartPt c (A u v))
        (u • ((realTangentCoords c (γ u)).comp (P u).toContinuousLinearMap)) 0)
    (hSecond : ∀ (c : Pt X) (u : ℝ), u ∈ Set.Ioo (-δ) (1+δ) →
      γ u ∈ (chartAt (ComplexVector n) c).source → ∀ w : ComplexVector n,
      HasDerivAt (deriv (fun r : ℝ => chartPt c (A u (r • w))))
        (-chartChristoffelBilin X.metric.form c (chartPt c (γ u))
          (u • realTangentCoords c (γ u) (P u w))
          (u • realTangentCoords c (γ u) (P u w))) 0)
    (u : ℝ) (hu : u ∈ Set.Ioo (-δ) (1+δ)) (v : ComplexVector n) :
    letI := manifold_realSmooth X.manifold
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ U) →
    deriv (deriv (fun r : ℝ => fieldPathSpeed X.metric.form (fun s => A s (r • v)) u ^ 2)) 0 +
      deriv (deriv (fun r : ℝ => fieldPathSpeed X.metric.form
        (fun s => A s (r • (Complex.I • v))) u ^ 2)) 0 ≤
      4 * realMetricInChart X.metric.form (γ 1) (chartPt (γ 1) (γ 1)) v v := by
  letI := manifold_realSmooth X.manifold
  intro hA
  have hh := metricSmooth_of_smoothMetric X.metric
  have hk : KahlerClosed X.metric.form := X.kahler_metric
  have hc : γ u ∈ (chartAt (ComplexVector n) (γ u)).source := mem_chart_source _ _
  have H₁ := fieldPathSpeedSq_parallelVariation_secondDeriv X.metric.form hh γ P A δ hδ
    U hU hzero hγ hA0 hP hFirst hSecond u hu (γ u) hc v hA
  have H₂ := fieldPathSpeedSq_parallelVariation_secondDeriv X.metric.form hh γ P A δ hδ
    U hU hzero hγ hA0 hP hFirst hSecond u hu (γ u) hc (Complex.I • v) hA
  have hJ := parallelEndpoint_coordinates_I X.metric.form hh hk γ P δ hδ hγ hP1 hP v u hu (γ u) hc
  have hcurv := paired_scaled_connectionCurvature_nonpos X (γ u)
    (geoChartState γ (γ u) u).2 (realTangentCoords (γ u) (γ u) (P u v)) u
  have hkin (w : ComplexVector n) :
      realMetricInChart X.metric.form (γ u) (chartPt (γ u) (γ u))
        (realTangentCoords (γ u) (γ u) (P u w))
        (realTangentCoords (γ u) (γ u) (P u w)) =
      realMetricInChart X.metric.form (γ 1) (chartPt (γ 1) (γ 1)) w w := by
    rw [realMetricInChart_tangentCoords X.metric.form (γ u) (γ u) hc]
    exact hPair u hu w w
  have hI : realMetricInChart X.metric.form (γ 1) (chartPt (γ 1) (γ 1))
      (Complex.I • v) (Complex.I • v) =
      realMetricInChart X.metric.form (γ 1) (chartPt (γ 1) (γ 1)) v v :=
    realMetricInChart_I X.metric.form (γ 1) (z := chartPt (γ 1) (γ 1))
      (mem_extChartAt_target (γ 1)) v
  rw [H₁,H₂,hkin v,hkin (Complex.I • v),hI,hJ]
  linarith

end Yau.NodeProofs.P07DistanceLevi
