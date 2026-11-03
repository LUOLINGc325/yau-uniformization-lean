import Yau.Proofs.F05PhysicalTraceJets
import Yau.LeafProofs.L16BoundaryTimeContinuation

/-! Restart slabs glue using equality of the actual physical trace.
Unique physical differentiation supplies both spatial jet matches; equality
of arbitrary ambient representatives is not required. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16BoundaryTimeAux
variable {n : ℕ}

theorem F05_c2_timePaste_physical {X : Set (Space n)} (hClosed : IsClosed X)
    (hX : UniqueDiffOn ℝ X) {τ T : ℝ} (hτ : 0 < τ) (hT : τ < T)
    {u v : Point n → ℝ} (hu : C2 (cylinder X 0 τ) u) (hv : C2 (cylinder X τ T) v)
    (hTrace : ∀ x ∈ X, u (x,τ) = v (x,τ))
    (htTrace : ∀ x ∈ X, timeD (cylinder X 0 τ) u (x,τ) = timeD (cylinder X τ T) v (x,τ)) :
    C2 (cylinder X 0 T) (timePaste τ u v) := by
  have hSpatial := F05_physical_trace_spatial_jets hX u v τ
    (fun x hx => hu.2.2.2.2.1 (x,τ) ⟨hx,hτ.le,le_rfl⟩)
    (fun x hx => hv.2.2.2.2.1 (x,τ) ⟨hx,le_rfl,hT.le⟩) hTrace
  refine ⟨continuousOn_timePaste_space hClosed hτ.le hT.le hu.1 hv.1 hTrace,?_,?_,?_,?_,?_⟩
  · rw [spatialD_timePaste]
    exact continuousOn_timePaste_space hClosed hτ.le hT.le hu.2.1 hv.2.1
      (fun x hx => (hSpatial x hx).1)
  · rw [spatialDD_timePaste]
    exact continuousOn_timePaste_space hClosed hτ.le hT.le hu.2.2.1 hv.2.2.1
      (fun x hx => (hSpatial x hx).2)
  · exact (continuousOn_timePaste_space hClosed hτ.le hT.le hu.2.2.2.1 hv.2.2.2.1 htTrace).congr
      (fun p hp => timeD_timePaste_space hτ hT hu hv hTrace htTrace hp)
  · intro p hp
    by_cases h : p.2 ≤ τ
    · simpa only [timePaste,ite_eq_left h] using hu.2.2.2.2.1 p ⟨hp.1,hp.2.1,h⟩
    · simpa only [timePaste,ite_eq_right h] using hv.2.2.2.2.1 p ⟨hp.1,(le_of_not_ge h),hp.2.2⟩
  · intro p hp
    have h := (timePaste_hasDerivWithinAt_space hτ hT hu hv hTrace htTrace hp).differentiableWithinAt
    simpa only [cylinder,mem_ofPred_eq,mem_prod,hp.1,true_and,ofPred_mem_eq] using h

end Yau.Proofs.F05Aux
