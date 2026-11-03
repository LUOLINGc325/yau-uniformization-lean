import Yau.LeafProofs.L23DistanceEnergySecondTrace

/-! No supplied second-variation estimate remains in the actual parallel energy trace. -/

noncomputable section
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

variable {n : ℕ} {M : ComplexManifold n}

theorem parallelEnergy_secondTrace_bound
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (A : ℝ → ComplexVector n → M.Carrier) (δ K d : ℝ) (hδ : 0<δ)
    (U : Set (ComplexVector n)) (hU : IsOpen U) (hzero : (0 : ComplexVector n)∈U)
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
      OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) (γ 1))) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ U) →
    (∑ i : Fin (2*n), deriv (deriv (fun r : ℝ => fieldPathEnergy h
      (fun u => A u (r • realTangentCoords (γ 1) (γ 1) (b i))))) 0)≤
        2*(2*n : ℕ)+(2/3 : ℝ)*(2*n : ℕ)*K*d^2 := by
  letI := manifold_realSmooth M
  intro hA
  have hunit : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-δ) (1+δ) := by
    intro u hu
    constructor <;> linarith [hu.1,hu.2]
  apply energySecondTrace_bound_of_densityFormula h hh γ P A δ K d hδ U hU hzero hγ
    (fun u hu => hPair u (hunit hu)) hcurv hspeed b _ hA
  intro u hu i
  exact fieldPathSpeedSq_parallelVariation_secondDeriv h hh γ P A δ hδ U hU hzero hγ hA0
    hP hFirst hSecond u (hunit hu) (γ u) (mem_chart_source _ _)
      (realTangentCoords (γ 1) (γ 1) (b i)) hA

end Yau.LeafProofs.L23Aux
