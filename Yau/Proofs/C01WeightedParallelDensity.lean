import Yau.Proofs.C01WeightedActualDensity
import Yau.Proofs.C01RayFamily

/-! The actual parallel-endpoint variation supplies the exact cutoff-weighted first and second energy jets. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
open Yau.LeafProofs.L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}

theorem indexWeighted_parallel_density_second_derivative
    (k : HermitianField M) (hk : MetricSmooth k) (γ : ℝ → M.Carrier)
    (P : (s : ℝ) → ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ s))
    (A : ℝ → ComplexVector n → M.Carrier) (δ : ℝ) (hδ : 0 < δ)
    (U : Set (ComplexVector n)) (hU : IsOpen U)
    (hγ : FieldGeodesicOn k γ (Set.Ioo (-δ) (1+δ)))
    (hA0 : ∀ s ∈ Set.Ioo (-δ) (1+δ), A s 0 = γ s)
    (hP : ∀ (c : M.Carrier) (s : ℝ), s ∈ Set.Ioo (-δ) (1+δ) →
      γ s ∈ (chartAt (ComplexVector n) c).source → ∀ w : ComplexVector n,
      HasDerivAt (fun r => realTangentCoords c (γ r) (P r w))
        (-chartChristoffelBilin k c (chartPt c (γ s)) (geoChartState γ c s).2
          (realTangentCoords c (γ s) (P s w))) s)
    (hFirst : ∀ (c : M.Carrier) (s : ℝ), s ∈ Set.Ioo (-δ) (1+δ) →
      γ s ∈ (chartAt (ComplexVector n) c).source →
      HasFDerivAt (fun v => chartPt c (A s v))
        (s • ((realTangentCoords c (γ s)).comp (P s).toContinuousLinearMap)) 0)
    (hSecond : ∀ (c : M.Carrier) (s : ℝ), s ∈ Set.Ioo (-δ) (1+δ) →
      γ s ∈ (chartAt (ComplexVector n) c).source → ∀ w : ComplexVector n,
      HasDerivAt (deriv (fun r : ℝ => chartPt c (A s (r • w))))
        (-chartChristoffelBilin k c (chartPt c (γ s))
          (s • realTangentCoords c (γ s) (P s w))
          (s • realTangentCoords c (γ s) (P s w))) 0)
    (κ : ℝ) (hκ : 0 < κ) (J' : Set ℝ) (U' : Set (ComplexVector n))
    (hJ' : IsOpen J') (hU' : IsOpen U') (hzero' : (0 : ComplexVector n) ∈ U')
    (hmap : Set.MapsTo (fun p : ℝ × ComplexVector n =>
      (p.1, indexCutoffRatio κ p.1 • p.2)) (J' ×ˢ U') (Set.Ioo (-δ) (1+δ) ×ˢ U))
    (u : ℝ) (hu : u ∈ J') (c : M.Carrier)
    (hc : γ u ∈ (chartAt (ComplexVector n) c).source) (w : ComplexVector n) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ U) →
    deriv (deriv (fun r : ℝ => actualPathSpeed k
      (fun s => weightedVariation A (indexCutoffRatio κ) s (r • w)) u ^ 2)) 0 =
      2 * realMetricInChart k c (chartPt c (γ u))
        (deriv (indexCutoff κ) u • realTangentCoords c (γ u) (P u w))
        (deriv (indexCutoff κ) u • realTangentCoords c (γ u) (P u w)) +
      2 * realMetricInChart k c (chartPt c (γ u)) (geoChartState γ c u).2
        (connectionCurvature (chartChristoffelBilin k c) (chartPt c (γ u))
          (indexCutoff κ u • realTangentCoords c (γ u) (P u w))
          (geoChartState γ c u).2 (indexCutoff κ u • realTangentCoords c (γ u) (P u w))) := by
  letI := manifold_realSmooth M
  intro hA
  let B := weightedVariation A (indexCutoffRatio κ)
  let F : ℝ → ℝ → M.Carrier := fun r s => B s (r • w)
  let V : ℝ → ComplexVector n := fun s => realTangentCoords c (γ s) (P s w)
  have hsub : J' ⊆ Set.Ioo (-δ) (1+δ) := fun s hs =>
    (hmap (show (s, (0 : ComplexVector n)) ∈ J' ×ˢ U' from ⟨hs, hzero'⟩)).1
  have hB := weightedVariation_contMDiffOn A (indexCutoffRatio κ)
    ((indexCutoffRatio_contDiff hκ).of_le (by simp)) _ J' U U' hmap hA
  have hF := rayFamily_contMDiffOn B J' U' w hB
  have hI := rayParameterDomain_isOpen U' hU' w
  have hIzero := rayParameterDomain_zero_mem U' hzero' w
  have hbase : ∀ s ∈ J', F 0 s = γ s := by
    intro s hs
    simp only [F, B, weightedVariation, zero_smul, smul_zero, hA0 s (hsub hs)]
  have hcont : ContinuousAt γ u := hγ.1.continuousOn.continuousAt (isOpen_Ioo.mem_nhds (hsub hu))
  have hsrc : ∀ᶠ s in 𝓝 u, γ s ∈ (chartAt (ComplexVector n) c).source :=
    hcont.preimage_mem_nhds ((chartAt (ComplexVector n) c).open_source.mem_nhds hc)
  have hf : ∀ᶠ s in 𝓝 u, HasDerivAt (fun r : ℝ => chartPt c (F r s))
      (indexCutoff κ s • V s) 0 := by
    filter_upwards [hsrc, isOpen_Ioo.mem_nhds (hsub hu)] with s hs hsI
    let Q := (realTangentCoords c (γ s)).comp (P s).toContinuousLinearMap
    have Hfirst (v : ComplexVector n) :
        HasDerivAt (fun r : ℝ => chartPt c (A s (r • v))) (s • Q v) 0 := by
      have H0 : HasFDerivAt (fun v => chartPt c (A s v)) (s • Q) ((0 : ℝ) • v) := by
        simpa only [zero_smul] using hFirst c s hsI hs
      have H := H0.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const v)
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.smul_apply, one_smul] using H
    have H := indexWeighted_radial_first (fun v => chartPt c (A s v)) Q κ s hκ w Hfirst
    simpa only [F, B, weightedVariation, Q, V, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] using H
  have hs : ∀ᶠ s in 𝓝 u,
      HasDerivAt (deriv (fun r : ℝ => chartPt c (F r s)))
        (-chartChristoffelBilin k c (chartPt c (γ s))
          (indexCutoff κ s • V s) (indexCutoff κ s • V s)) 0 := by
    filter_upwards [hsrc, isOpen_Ioo.mem_nhds (hsub hu)] with s hs hsI
    let Q := (realTangentCoords c (γ s)).comp (P s).toContinuousLinearMap
    have Hsecond (v : ComplexVector n) :
        HasDerivAt (deriv (fun r : ℝ => chartPt c (A s (r • v))))
          (-chartChristoffelBilin k c (chartPt c (γ s)) (s • Q v) (s • Q v)) 0 :=
      hSecond c s hsI hs v
    have H := indexWeighted_radial_second (fun v => chartPt c (A s v)) Q
      (chartChristoffelBilin k c (chartPt c (γ s))) κ s hκ w Hsecond
    simpa only [F, B, weightedVariation, Q, V, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] using H
  have hφ : HasDerivAt (indexCutoff κ) (deriv (indexCutoff κ) u) u :=
    ((indexCutoff_contDiff κ).differentiable (by simp) u).hasDerivAt
  exact weighted_actual_density_second_derivative k hk F γ (rayParameterDomain U' w) J'
    hI hJ' hIzero hbase (indexCutoff κ) (deriv (indexCutoff κ) u) u hu c hc V hφ
    hf hs (hP c u (hsub hu) hc w) hF

end Yau.NodeProofs.C01Aux
