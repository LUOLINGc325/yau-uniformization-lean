import Yau.LeafProofs.L23DistanceEnergySecondTraceActual

/-! The actual second-variation integral bounds the original scalar Laplacian. -/

noncomputable section
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {n : ℕ} {M : ComplexManifold n}

theorem realLap_endpointVariation_fieldPathEnergy_le_of_trace
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (A : ℝ → ComplexVector n → M.Carrier) (δ K d : ℝ) (hδ : 0<δ)
    (hzero : (0 : ComplexVector n)∈e.source)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ)))
    (hA0 : ∀ u∈Set.Ioo (-δ) (1+δ), A u 0=γ u)
    (hPair : ∀ u∈Set.Ioo (-δ) (1+δ), ∀ v w : ComplexVector n,
      (underlyingRealRiemannianMetric h).inner (γ u) (P u v) (P u w)=
        realMetricInChart h (γ 1) (chartPt (γ 1) (γ 1)) v w)
    (hP : ∀ (c : M.Carrier) (u : ℝ), u∈Set.Ioo (-δ) (1+δ) → γ u∈(chartAt (ComplexVector n) c).source →
      ∀ w : ComplexVector n, HasDerivAt (fun s => realTangentCoords c (γ s) (P s w))
        (-chartChristoffelBilin h c (chartPt c (γ u)) (geoChartState γ c u).2
          (realTangentCoords c (γ u) (P u w))) u)
    (hFirst : ∀ (c : M.Carrier) (u : ℝ), u∈Set.Ioo (-δ) (1+δ) → γ u∈(chartAt (ComplexVector n) c).source →
      HasFDerivAt (fun v => chartPt c (A u v))
        (u • ((realTangentCoords c (γ u)).comp (P u).toContinuousLinearMap)) 0)
    (hSecond : ∀ (c : M.Carrier) (u : ℝ), u∈Set.Ioo (-δ) (1+δ) → γ u∈(chartAt (ComplexVector n) c).source →
      ∀ w : ComplexVector n, HasDerivAt (deriv (fun r : ℝ => chartPt c (A u (r • w))))
        (-chartChristoffelBilin h c (chartPt c (γ u))
          (u • realTangentCoords c (γ u) (P u w)) (u • realTangentCoords c (γ u) (P u w))) 0)
    (hcurv : ∀ u∈Set.Icc (0 : ℝ) 1, curvatureJetNorm h 0 (γ u)≤K)
    (hspeed : ∀ u∈Set.Icc (0 : ℝ) 1, actualSpeedSq h γ u=d^2)
    (b : letI := underlyingRealTangentNormedAddCommGroup h (γ 1)
      letI := underlyingRealTangentInnerProductSpace h (γ 1)
      OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) (γ 1)))
    (hTrace : realLap h (fun z => fieldPathEnergy h (fun u => A u (e.symm z))) (γ 1)=
      ∑ i : Fin (2*n), deriv (deriv (fun r : ℝ => fieldPathEnergy h
        (fun u => A u (r • realTangentCoords (γ 1) (γ 1) (b i))))) 0) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ e.source) →
    realLap h (fun z => fieldPathEnergy h (fun u => A u (e.symm z))) (γ 1)≤
      2*(2*n : ℕ)+(2/3 : ℝ)*(2*n : ℕ)*K*d^2 := by
  letI := manifold_realSmooth M
  intro hA
  rw [hTrace]
  exact parallelEnergy_secondTrace_bound h hh γ P A δ K d hδ e.source e.open_source hzero hγ hA0
    hPair hP hFirst hSecond hcurv hspeed b hA

end Yau.LeafProofs.L23Aux
