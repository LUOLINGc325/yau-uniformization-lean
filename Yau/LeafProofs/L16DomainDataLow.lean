import Yau.LeafProofs.L16BoundaryPhysicalData
import Yau.LeafProofs.L16InteriorDataLow
import Yau.LeafProofs.L16FiniteDataHolderGluing

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance domainDataLow_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance domainDataLow_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

/-- On the actual closure of a smooth bounded domain, the frozen parabolic
    Schauder data norm controls both lower jets in Holder norm. The constant
    is chosen before the datum, with no mixed derivative or extension assumed. -/
theorem smoothDomain_data_lowPair_holder {n : ℕ} {O : Set (Space n)} (hO : SmoothDomain O)
    {α T : ℝ} (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Point n → ℝ) P,
      SchauderBound α (cylinder (closure O) 0 T) u P →
      HolderBound α (cylinder (closure O) 0 T) (fun p => (u p,spatialD u p)) (C*P) := by
  classical
  have hLocal (i : closure O) : ∃ r A : ℝ, 0 < r ∧ 0 < A ∧
      ∀ (u : Point n → ℝ) P, SchauderBound α (cylinder (closure O) 0 T) u P →
        HolderBound α (cylinder (closure O∩Metric.closedBall (i : Space n) r) 0 T)
          (fun p => (u p,spatialD u p)) (A*P) := by
    by_cases hi : (i : Space n) ∈ O
    · obtain ⟨r,A,hr,hA,hBuffer,hInterior⟩ := open_interior_data_low_holder hO.1 hi hα hα1 hT
      exact ⟨r,A,hr,hA,fun u P hu => holderBound_mono (hInterior u P hu)
        (fun p hp => ⟨hp.1.2,hp.2⟩)⟩
    · have hiF : (i : Space n) ∈ frontier O := by
        rw [frontier,hO.1.interior_eq]
        exact ⟨i.2,hi⟩
      exact smoothDomain_boundary_data_low_holder hO hiF hα hα1 hT
  choose r A hr hA hLocalBound using hLocal
  obtain ⟨C,hC,hGlue⟩ := compact_spatial_local_holder_glue (E := ℝ×(Space n →L[ℝ] ℝ)) hO.2.2.1 hα.le r A hr (fun i => (hA i).le)
  refine ⟨C,hC,?_⟩
  intro u P hu
  exact hGlue (fun p => (u p,spatialD u p)) P hu.2.1
    (fun p hp => max_le (hu.2.2.1 p hp).1 (hu.2.2.1 p hp).2)
    (fun i => hLocalBound i u P hu)

end Yau.LeafProofs.L16Aux
