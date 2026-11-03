import spec.CHAIN.CONTRACTS
import Yau.LeafProofs.L18

noncomputable section
open MeasureTheory
open scoped Topology Manifold ENNReal Matrix

namespace Yau.Proofs.G02Aux
open Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

def chartSource (a : M.Carrier) : Set M.Carrier :=
  (extChartAt (ComplexModel n) a).source

def density (h : HermitianField M) (a : M.Carrier) (z : ComplexVector n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (realMetricFn h a z).det)

def localVolume (h : HermitianField M) (a : M.Carrier) : Measure M.Carrier :=
  Measure.map (L18Aux.chartInvExtension a)
    (((lebesgueC n).restrict (chartTarget a)).withDensity (density h a))

theorem measurableSet_chartSource (a : M.Carrier) : MeasurableSet (chartSource a) :=
  (isOpen_extChartAt_source (I := ComplexModel n) a).measurableSet

theorem chart_image_eq_preimage (a : M.Carrier) (s : Set M.Carrier)
    (hsa : s ⊆ chartSource a) :
    chartPt a '' s = L18Aux.chartInvExtension a ⁻¹' s ∩ chartTarget a := by
  have hi : s ∩ (extChartAt (ComplexModel n) a).source = s :=
    Set.inter_eq_left.mpr hsa
  simpa only [hi] using L18Aux.chart_image_eq_extension_preimage a s

theorem measurableSet_chart_image (a : M.Carrier) (s : Set M.Carrier)
    (hs : MeasurableSet s) (hsa : s ⊆ chartSource a) :
    MeasurableSet (chartPt a '' s) := by
  rw [chart_image_eq_preimage a s hsa]
  exact ((L18Aux.chartInvExtension_measurable a) hs).inter
    (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet

theorem localVolume_apply (h : HermitianField M) (a : M.Carrier)
    (s : Set M.Carrier) (hs : MeasurableSet s) :
    localVolume h a s =
      ∫⁻ z in chartPt a '' (s ∩ chartSource a), density h a z ∂lebesgueC n := by
  rw [localVolume, Measure.map_apply (L18Aux.chartInvExtension_measurable a) hs,
    withDensity_apply _ ((L18Aux.chartInvExtension_measurable a) hs),
    Measure.restrict_restrict ((L18Aux.chartInvExtension_measurable a) hs),
    ← L18Aux.chart_image_eq_extension_preimage a s]
  rfl

theorem localVolume_apply_of_subset (h : HermitianField M) (a : M.Carrier)
    (s : Set M.Carrier) (hs : MeasurableSet s) (hsa : s ⊆ chartSource a) :
    localVolume h a s = ∫⁻ z in chartPt a '' s, density h a z ∂lebesgueC n := by
  simpa only [Set.inter_eq_left.mpr hsa] using localVolume_apply h a s hs

theorem localVolume_restrict_source (h : HermitianField M) (a : M.Carrier) :
    (localVolume h a).restrict (chartSource a) = localVolume h a := by
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs,
    localVolume_apply h a (s ∩ chartSource a) (hs.inter (measurableSet_chartSource a)),
    localVolume_apply h a s hs]
  simp only [Set.inter_assoc, Set.inter_self]

end Yau.Proofs.G02Aux
