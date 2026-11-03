import Yau.Proofs.C06Curvature
import Yau.Proofs.P07DistanceLeviComparison

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold
namespace Yau.Proofs.C06Aux
open Yau Yau.Blueprint Yau.NodeProofs Yau.NodeProofs.P07DistanceLevi
open Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
variable {n : ℕ}

theorem parallelVariation_paired_secondDensity_lt
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
    (u : ℝ) (hu : u ∈ Set.Ioo (-δ) (1+δ)) (v : ComplexVector n)
    (hT : (geoChartState γ (γ u) u).2 ≠ 0) (hv : v ≠ 0) (hu0 : u ≠ 0) :
    letI := manifold_realSmooth X.manifold
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ U) →
    deriv (deriv (fun r : ℝ => fieldPathSpeed X.metric.form (fun s => A s (r • v)) u ^ 2)) 0 +
      deriv (deriv (fun r : ℝ => fieldPathSpeed X.metric.form
        (fun s => A s (r • (Complex.I • v))) u ^ 2)) 0 <
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
  have hV : realTangentCoords (γ u) (γ u) (P u v) ≠ 0 := by
    intro hzeroV
    have H := congrArg (realFrameCLM (γ u) (γ u)) hzeroV
    have Hp : P u v = 0 := by
      simpa only [realFrameCLM_realTangentCoords (γ u) (γ u) hc, map_zero] using H
    exact hv ((P u).injective (Hp.trans (map_zero _).symm))
  have hcurv := paired_scaled_connectionCurvature_neg X (γ u) hT hV hu0
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


end Yau.Proofs.C06Aux
