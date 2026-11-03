import Yau.LeafProofs.L12CutBoundary
import Yau.LeafProofs.L09
import Mathlib.MeasureTheory.Function.Jacobian

/-! Nullity of the image of the genuine radial cut-endpoint vectors.
The only geometric inputs are the actual C1 exponential and tangent-Haar
nullity; chartwise differentiable null-image preservation supplies the rest. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

set_option backward.isDefEq.respectTransparency false in
/-- The Riemannian chart law also kills arbitrary sets with null coordinate
image: a measurable null envelope avoids any completeness assumption on μ. -/
theorem measure_eq_zero_of_chart_image_eq_zero
    (h : HermitianField M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume h μ)
    (y : M.Carrier) (s : Set M.Carrier)
    (hs : s ⊆ (chartAt (ComplexVector n) y).source)
    (hzero : lebesgueC n (chartPt y '' s) = 0) : μ s = 0 := by
  classical
  let U := (chartAt (ComplexVector n) y).source
  let C : M.Carrier → ComplexVector n := U.piecewise (chartPt y) (fun _ => 0)
  let B := toMeasurable (lebesgueC n) (chartPt y '' s)
  have hU : MeasurableSet U := (chartAt (ComplexVector n) y).open_source.measurableSet
  have hchart : ContinuousOn (chartPt y) U := by
    change ContinuousOn (extChartAt (ComplexModel n) y)
      (chartAt (ComplexVector n) y).source
    rw [← extChartAt_source (ComplexModel n)]
    exact continuousOn_extChartAt y
  have hC : Measurable C := hchart.measurable_piecewise continuousOn_const hU
  let T := U ∩ C ⁻¹' B
  have hT : MeasurableSet T := hU.inter (hC (measurableSet_toMeasurable _ _))
  have hsub : s ⊆ T := by
    intro z hz
    refine ⟨hs hz, ?_⟩
    change C z ∈ B
    simpa only [C, piecewise_eq_of_mem U (chartPt y) (fun _ => 0) (hs hz)] using
      (subset_toMeasurable (lebesgueC n) (chartPt y '' s) (mem_image_of_mem (chartPt y) hz))
  have him : chartPt y '' T ⊆ B := by
    rintro _ ⟨z, hz, rfl⟩
    have hzB : C z ∈ B := hz.2
    simpa only [C, piecewise_eq_of_mem U (chartPt y) (fun _ => 0) hz.1] using hzB
  have hB : lebesgueC n B = 0 := by
    simpa only [B, measure_toMeasurable] using hzero
  apply measure_mono_null hsub
  rw [hμ y T hT inter_subset_left]
  exact setLIntegral_measure_zero _ _ (measure_mono_null him hB)

set_option backward.isDefEq.respectTransparency false in
/-- A C1 map from the real coordinate model into the manifold sends a
Lebesgue-null set to a null set for every measure satisfying the volume law. -/
theorem contMDiff_image_measure_zero_of_isRiemannianVolume
    (h : HermitianField M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume h μ)
    (f : ComplexVector n → M.Carrier) :
    letI := manifold_realSmooth M
    ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 f →
      ∀ s : Set (ComplexVector n), volume s = 0 → μ (f '' s) = 0 := by
  letI := manifold_realSmooth M
  intro hf s hs
  have hlocal (y : M.Carrier) : μ ((f '' s) ∩ (chartAt (ComplexVector n) y).source) = 0 := by
    let A := s ∩ f ⁻¹' (chartAt (ComplexVector n) y).source
    have hA : volume A = 0 := measure_mono_null inter_subset_left hs
    have hdiff : DifferentiableOn ℝ (fun v => chartPt y (f v)) A := by
      intro v hv
      have hc : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1
          (chartPt y) (f v) :=
        contMDiffAt_extChartAt' (by simpa only [extChartAt_source, mem_preimage] using hv.2)
      exact ((hc.comp v hf.contMDiffAt).contDiffAt.differentiableAt (by simp)).differentiableWithinAt
    have hcoord : volume ((fun v => chartPt y (f v)) '' A) = 0 :=
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hA
    apply measure_eq_zero_of_chart_image_eq_zero h μ hμ y _ inter_subset_right
    rw [lebesgueC_eq_volume]
    apply measure_mono_null _ hcoord
    rintro _ ⟨z, ⟨⟨v, hv, rfl⟩, hz⟩, rfl⟩
    exact ⟨v, ⟨hv, hz⟩, rfl⟩
  obtain ⟨r, hr, hcover⟩ := isLindelof_univ.elim_countable_subcover
    (fun y : M.Carrier => (chartAt (ComplexVector n) y).source)
    (fun y => (chartAt (ComplexVector n) y).open_source)
    (by intro z _; exact mem_iUnion.mpr ⟨z, mem_chart_source _ _⟩)
  have hnull : μ (⋃ y ∈ r, (f '' s) ∩ (chartAt (ComplexVector n) y).source) = 0 :=
    (measure_biUnion_null_iff hr).mpr (fun y _ => hlocal y)
  apply measure_mono_null _ hnull
  intro z hz
  obtain ⟨y, hyr, hyz⟩ := mem_iUnion₂.mp (hcover (mem_univ z))
  exact mem_iUnion₂.mpr ⟨y, hyr, hz, hyz⟩

/-- The actual cut-endpoint vectors have a null image under the actual
Riemannian exponential, without nonconjugacy or a supplied volume formula. -/
theorem realExponentialMap_cutEndpointVectors_image_measure_zero
    (g : SmoothMetric M) (x : M.Carrier) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) :
    μ (realExponentialMap g x '' realCutEndpointVectors g x) = 0 := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
  let e : ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) x :=
    ContinuousLinearEquiv.equivOfInverse (realFrameCLM x x) (realTangentCoords x x)
      (realTangentCoords_realFrameCLM x x (mem_chart_source _ _))
      (realFrameCLM_realTangentCoords x x (mem_chart_source _ _))
  let ν : Measure (TangentSpace 𝓘(ℝ, ComplexVector n) x) := volume.map e
  have hν := realCutEndpointVectors_measure_zero g x ν (by dsimp [ν]; infer_instance)
  have hcut : MeasurableSet (realCutEndpointVectors g x) :=
    (isClosed_realMinimizingVectors g x).measurableSet.diff
      (measurableSet_realStrictMinimizingVectors g x)
  have hs : volume (e ⁻¹' realCutEndpointVectors g x) = 0 := by
    change (volume.map e) (realCutEndpointVectors g x) = 0 at hν
    rwa [Measure.map_apply e.continuous.measurable hcut] at hν
  have hf : ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1
      (realExponentialMap g x ∘ e) :=
    (realExponentialMap_contMDiff g x).comp e.toContinuousLinearMap.contMDiff
  have hnull := contMDiff_image_measure_zero_of_isRiemannianVolume g.form μ hμ
    (realExponentialMap g x ∘ e) hf (e ⁻¹' realCutEndpointVectors g x) hs
  have heq : (realExponentialMap g x ∘ e) '' (e ⁻¹' realCutEndpointVectors g x) =
      realExponentialMap g x '' realCutEndpointVectors g x := by
    rw [image_comp, e.surjective.image_preimage]
  rwa [heq] at hnull

end Yau.LeafProofs.L12Aux
