import Yau.LeafProofs.L23FieldMetricSpray
import Yau.LeafProofs.L23LocalDistanceSupportEnergy
import Yau.LeafProofs.L23TensorAlgebra
import Yau.LeafProofs.L12ODEVariation

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ContDiff
namespace Yau.LeafProofs.L23LocalDistanceContract
open Yau.LeafProofs.L12Aux

variable {n : ℕ} {M : ComplexManifold n}

def geoChartState (γ : ℝ → M.Carrier) (c : M.Carrier) (u : ℝ) :
    ComplexVector n × ComplexVector n :=
  (chartPt c (γ u), deriv (fun s => chartPt c (γ s)) u)

/-- An actual geodesic equation in every chart that contains the point. -/
def FieldGeodesicOn (h : HermitianField M) (γ : ℝ → M.Carrier)
    (J : Set ℝ) : Prop :=
  letI := manifold_realSmooth M
  ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ J ∧
    ∀ (c : M.Carrier) (u : ℝ), u ∈ J →
      γ u ∈ (extChartAt (ComplexModel n) c).source →
      HasDerivAt (geoChartState γ c)
        (chartGeodesicSpray h c (geoChartState γ c u)) u

/-- This is exactly G(γ',γ'), with G=2 Re h. -/
def actualSpeedSq (h : HermitianField M) (γ : ℝ → M.Carrier) (u : ℝ) : ℝ :=
  (underlyingRealRiemannianMetric h).inner (γ u)
    (realCurveVelocity γ u) (realCurveVelocity γ u)

/-- Card N. X solves the actual spray, and e is its actual endpoint IFT. -/
def LocalNormalEndpointGap (n : ℕ) : Prop :=
  ∀ (M : ComplexManifold n) (h : HermitianField M), MetricSmooth h →
    ∀ (c : M.Carrier) (O : Set M.Carrier), IsOpen O → c ∈ O →
    ∃ (B : Set (ComplexVector n)) (ρ ε : ℝ)
      (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
      (e : OpenPartialHomeomorph
        (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n)),
      IsOpen B ∧ chartPt c c ∈ B ∧ B ⊆ chartTarget c ∧
      0 < ρ ∧ 0 < ε ∧
      e.source = B ×ˢ Metric.ball (0 : ComplexVector n) ρ ∧
      Set.EqOn e (fun p => (p.1, X p 1)) e.source ∧
      ContDiffOn ℝ 3 (Function.uncurry X)
        (e.source ×ˢ Set.Ioo (-ε) (1+ε)) ∧
      ContDiffOn ℝ 3 e.symm e.target ∧
      (∀ p ∈ e.source,
        X p 0 = p.1 ∧ deriv (X p) 0 = p.2 ∧
        (∀ u ∈ Set.Ioo (-ε) (1+ε), X p u ∈ chartTarget c) ∧
        FieldGeodesicOn h (fun u => chartInv c (X p u))
          (Set.Ioo (-ε) (1+ε)) ∧
        Set.MapsTo (fun u => chartInv c (X p u)) (Set.Icc (0 : ℝ) 1) O ∧
        inducedDistance h (chartInv c p.1) (chartInv c (X p 1)) ^ 2 =
          realMetricInChart h c p.1 p.2 p.2) ∧
      (∀ z ∈ B,
        (∀ u ∈ Set.Ioo (-ε) (1+ε), X (z,0) u = z) ∧
        HasFDerivAt (fun v => X (z,v) 1)
          (ContinuousLinearMap.id ℝ (ComplexVector n)) 0)

/-- Card M. Compact confinement of true near-minimizers suffices. -/
def CompactMinimizingGeodesicGap (n : ℕ) : Prop :=
  ∀ (M : ComplexManifold n) (h : HermitianField M), MetricSmooth h →
    ∀ (O S : Set M.Carrier), IsOpen O → IsCompact S → S ⊆ O →
    ∀ (q y : M.Carrier),
      (∀ ε : ℝ, 0 < ε → ∃ β : IntegrableCurve h q y,
        curveLength h β.1 < inducedDistance h q y + ε ∧
        Set.MapsTo β.1 (Set.Icc (0 : ℝ) 1) S) →
      ∃ δ : ℝ, 0 < δ ∧ ∃ γ : ℝ → M.Carrier,
        γ 0 = q ∧ γ 1 = y ∧
        FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ)) ∧
        Set.MapsTo γ (Set.Icc (0 : ℝ) 1) O ∧
        ∀ u ∈ Set.Icc (0 : ℝ) 1,
          actualSpeedSq h γ u = inducedDistance h q y ^ 2

/-- Card V, static construction only: no flow, K, distance support or cutoff
    bound occurs in this Gap. P and A are actual transport/variation data. -/
def ParallelEndpointVariationGap (n : ℕ) : Prop :=
  ∀ (M : ComplexManifold n) (h : HermitianField M), MetricSmooth h →
    ∀ (O : Set M.Carrier), IsOpen O →
    ∀ (γ : ℝ → M.Carrier) (ε : ℝ), 0 < ε →
      FieldGeodesicOn h γ (Set.Ioo (-ε) (1+ε)) →
      Set.MapsTo γ (Set.Icc (0 : ℝ) 1) O →
      letI := manifold_realSmooth M
      ∃ (δ : ℝ) (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
        (P : (u : ℝ) → ComplexVector n ≃L[ℝ]
          TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
        (A : ℝ → ComplexVector n → M.Carrier),
        0 < δ ∧ δ < ε ∧ (0 : ComplexVector n) ∈ e.source ∧ e 0 = γ 1 ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n))
          𝓘(ℝ, ComplexVector n) 3 (Function.uncurry A)
          (Set.Ioo (-δ) (1+δ) ×ˢ e.source) ∧
        ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n)
          3 e.symm e.target ∧
        (∀ u ∈ Set.Ioo (-δ) (1+δ), A u 0 = γ u) ∧
        (∀ v ∈ e.source, A 0 v = γ 0 ∧ A 1 v = e v ∧
          Set.MapsTo (fun u => A u v) (Set.Icc (0 : ℝ) 1) O) ∧
        (P 1).toContinuousLinearMap = realFrameCLM (γ 1) (γ 1) ∧
        (∀ u ∈ Set.Ioo (-δ) (1+δ), ∀ v w : ComplexVector n,
          (underlyingRealRiemannianMetric h).inner (γ u) (P u v) (P u w) =
            realMetricInChart h (γ 1) (chartPt (γ 1) (γ 1)) v w) ∧
        (∀ (c : M.Carrier) (u : ℝ), u ∈ Set.Ioo (-δ) (1+δ) →
          γ u ∈ (extChartAt (ComplexModel n) c).source →
          (∀ w : ComplexVector n,
            HasDerivAt (fun s => realTangentCoords c (γ s) (P s w))
              (-chartChristoffelBilin h c (chartPt c (γ u))
                (geoChartState γ c u).2 (realTangentCoords c (γ u) (P u w))) u) ∧
          HasFDerivAt (fun v => chartPt c (A u v))
            (u • ((realTangentCoords c (γ u)).comp (P u).toContinuousLinearMap)) 0 ∧
          (∀ w : ComplexVector n,
            HasDerivAt (deriv (fun r : ℝ => chartPt c (A u (r • w))))
              (-chartChristoffelBilin h c (chartPt c (γ u))
                (u • realTangentCoords c (γ u) (P u w))
                (u • realTangentCoords c (γ u) (P u w))) 0))

end Yau.LeafProofs.L23LocalDistanceContract

namespace Yau.LeafProofs.L23Aux
open Yau.LeafProofs.L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}

/-- The precise compact-minimizer subproblem consumes the proved local
confinement data. Its geometric content is an explicit ordinary parameter. -/
theorem exists_buffered_minimizing_geodesic_of_gap
    (hgap : CompactMinimizingGeodesicGap n)
    (h : ℝ → HermitianField M) (p q y : M.Carrier)
    (a K r τ σ rIn rOut t : ℝ)
    (hK : 0 < K) (hr : 0 < r) (hτ : 0 < τ) (hσ : 0 < σ)
    (hO : IsOpen (distBall (h a) p (2*r)))
    (hcO : IsCompact (closure (distBall (h a) p (2*r))))
    (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ)
    (hcurv : ∀ x ∈ distBall (h a) p (2*r), ∀ s ∈ Set.Icc a (a+2*τ),
      curvatureJetNorm (h s) 0 x ≤ K)
    (hIn : 0 < rIn) (hInOut : rIn < rOut) (hOut : rOut ≤ 2*r)
    (hq : q ∈ distBall (h a) p rIn) (ht : t ∈ Set.Icc a (a+2*τ))
    (hy : inducedDistance (h t) q y < Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ : ℝ → M.Carrier,
      γ 0 = q ∧ γ 1 = y ∧ FieldGeodesicOn (h t) γ (Set.Ioo (-δ) (1+δ)) ∧
      Set.MapsTo γ (Set.Icc (0 : ℝ) 1) (distBall (h a) p (2*r)) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        actualSpeedSq (h t) γ u = inducedDistance (h t) q y ^ 2 := by
  have ha : a ∈ Set.Icc a (a+2*τ) := ⟨le_rfl,by linarith⟩
  have hS := fieldDistanceBuffer_isCompact (h a) (metricFamilySmooth_slice h hflow.1 ha)
    p hIn hInOut hOut hcO
  have hSO : fieldDistanceBuffer (h a) p rIn rOut ⊆ distBall (h a) p (2*r) := by
    intro z hz
    apply (mem_distBall_iff (h a) p z (by positivity)).mpr
    exact hz.trans_lt (by linarith)
  apply hgap M (h t) (metricFamilySmooth_slice h hflow.1 ht)
    (distBall (h a) p (2*r)) (fieldDistanceBuffer (h a) p rIn rOut) hO hS hSO q y
  intro ε hε
  obtain ⟨β,hβ,himage⟩ := exists_nearMinimizingCurve_in_buffer h p q y a K r τ σ rIn rOut t
    hK hr hτ hσ hflow hcurv hIn hInOut hOut hq ht hy hε
  exact ⟨β,hβ,himage⟩

end Yau.LeafProofs.L23Aux
