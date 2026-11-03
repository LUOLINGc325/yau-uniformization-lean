import Yau.LeafProofs.L23FieldMetricParallelGlobal

/-! Metric preservation for the genuine frame-valued parallel equation. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem parallelFrame_pairing_hasDerivAt
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (I : Set ℝ) (hI : IsOpen I) (HP : IsParallelFrameOn h γ P I) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ I →
    ∀ (t : ℝ), t ∈ I → ∀ v w : ComplexVector n,
      HasDerivAt (fun u => (underlyingRealRiemannianMetric h).inner (γ u) (P u v) (P u w)) 0 t := by
  letI := manifold_realSmooth M
  intro hγ t ht v w
  let c := γ t
  have hc : γ t ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  let K := I ∩ γ ⁻¹' (chartAt (ComplexVector n) c).source
  have hK : IsOpen K := hγ.continuousOn.isOpen_inter_preimage hI (chartAt (ComplexVector n) c).open_source
  have htK : t ∈ K := ⟨ht,hc⟩
  have Hcoord := curve_coordinates_contDiffOn_three γ c K hK (hγ.mono (fun u hu => hu.1)) (fun u hu => hu.2)
  have HD := ((Hcoord.contDiffAt (hK.mem_nhds htK)).differentiableAt (by norm_num)).hasDerivAt
  have hz : chartPt c (γ t) ∈ chartTarget c :=
    (extChartAt (ComplexModel n) c).map_source (by simpa only [extChartAt_source] using hc)
  have Hvec (V : ComplexVector n) :
      HasDerivAt (fun u => realTangentCoords c (γ u) (P u V))
        (-chartChristoffelBilin h c (chartPt c (γ t))
          (deriv (fun u => chartPt c (γ u)) t) (realTangentCoords c (γ t) (P t V))) t := by
    convert! (HP c t ht hc).clm_apply (hasDerivAt_const t V) using 1 <;>
      simp only [chartParallelCoefficient,ContinuousLinearMap.comp_apply,ContinuousLinearMap.neg_apply,
        map_zero,zero_add,add_zero]
  have H := realMetricInChart_parallelPair_hasDerivAt h hh c hz HD (Hvec v) (Hvec w)
  apply H.congr_of_eventuallyEq
  filter_upwards [hK.mem_nhds htK] with u hu
  exact (realMetricInChart_tangentCoords h c (γ u) hu.2 (P u v) (P u w)).symm

theorem parallelFrame_pairing_constant
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (a b : ℝ) (HP : IsParallelFrameOn h γ P (Set.Ioo a b)) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ (Set.Ioo a b) →
    ∀ (s t : ℝ), s ∈ Set.Ioo a b → t ∈ Set.Ioo a b → ∀ v w : ComplexVector n,
      (underlyingRealRiemannianMetric h).inner (γ s) (P s v) (P s w) =
        (underlyingRealRiemannianMetric h).inner (γ t) (P t v) (P t w) := by
  letI := manifold_realSmooth M
  intro hγ s t hs ht v w
  have H := parallelFrame_pairing_hasDerivAt h hh γ P _ isOpen_Ioo HP hγ
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun u hu => (H u hu v w).differentiableAt.differentiableWithinAt)
    (fun u hu => (H u hu v w).deriv) hs ht

end Yau.LeafProofs.L23Aux
