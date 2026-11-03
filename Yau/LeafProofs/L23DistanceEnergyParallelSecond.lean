import Yau.LeafProofs.L23DistanceEnergyActualVariation
import Yau.LeafProofs.L23LocalDistanceSupportContracts

/-! The actual static parallel endpoint variation supplies every second-variation input. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {n : ℕ} {M : ComplexManifold n}

theorem fieldPathSpeedSq_parallelVariation_secondDeriv
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (A : ℝ → ComplexVector n → M.Carrier) (δ : ℝ) (hδ : 0<δ)
    (U : Set (ComplexVector n)) (hU : IsOpen U) (hzero : (0 : ComplexVector n)∈U)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ)))
    (hA0 : ∀ u∈Set.Ioo (-δ) (1+δ), A u 0=γ u)
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
    (u : ℝ) (hu : u∈Set.Ioo (-δ) (1+δ)) (c : M.Carrier)
    (hc : γ u∈(chartAt (ComplexVector n) c).source) (w : ComplexVector n) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ U) →
    deriv (deriv (fun r : ℝ => fieldPathSpeed h (fun s => A s (r • w)) u^2)) 0=
      2*realMetricInChart h c (chartPt c (γ u))
        (realTangentCoords c (γ u) (P u w)) (realTangentCoords c (γ u) (P u w))+
      2*realMetricInChart h c (chartPt c (γ u)) (geoChartState γ c u).2
        (connectionCurvature (chartChristoffelBilin h c) (chartPt c (γ u))
          (u • realTangentCoords c (γ u) (P u w)) (geoChartState γ c u).2
          (u • realTangentCoords c (γ u) (P u w))) := by
  letI := manifold_realSmooth M
  intro hA
  let V : ℝ → ComplexVector n := fun s => realTangentCoords c (γ s) (P s w)
  have hcont : ContinuousAt γ u := hγ.1.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hu)
  have hsrc : ∀ᶠ s in 𝓝 u, γ s∈(chartAt (ComplexVector n) c).source :=
    hcont.preimage_mem_nhds ((chartAt (ComplexVector n) c).open_source.mem_nhds hc)
  have hf : ∀ᶠ s in 𝓝 u, HasDerivAt (fun r : ℝ => chartPt c (A s (r • w))) (s • V s) 0 := by
    filter_upwards [hsrc,isOpen_Ioo.mem_nhds hu] with s hs hsI
    have HH := hFirst c s hsI hs
    have H0 : HasFDerivAt (fun v => chartPt c (A s v))
        (s • ((realTangentCoords c (γ s)).comp (P s).toContinuousLinearMap)) ((0 : ℝ) • w) := by
      simpa only [zero_smul] using HH
    have H := H0.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const w)
    convert H using 1
    · rfl
    · simp only [V,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,one_smul,
        ContinuousLinearEquiv.coe_coe]
  have hs : ∀ᶠ s in 𝓝 u,
      HasDerivAt (deriv (fun r : ℝ => chartPt c (A s (r • w))))
        (-chartChristoffelBilin h c (chartPt c (γ s)) (s • V s) (s • V s)) 0 := by
    filter_upwards [hsrc,isOpen_Ioo.mem_nhds hu] with s hs hsI
    exact hSecond c s hsI hs w
  exact rayEnergyDensity_secondDeriv h hh A γ _ U isOpen_Ioo hU hzero hA0 w u hu c hc V
    hf hs (hP c u hu hc w) hA

end Yau.LeafProofs.L23Aux
