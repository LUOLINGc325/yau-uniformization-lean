import Yau.Proofs.F05PhysicalTimePaste

/-! A genuine physical-trace restart retains finite closed-corner
Schauder regularity, without equal arbitrary exterior representatives. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16BoundaryTimeAux
variable {n : ℕ}

theorem F05_schauder_timePaste_physical {X : Set (Space n)} (hClosed : IsClosed X)
    (hX : UniqueDiffOn ℝ X) {τ T α C D : ℝ} (hτ : 0 < τ) (hT : τ < T) (hα : 0 < α)
    {u v : Point n → ℝ} (hu : SchauderBound α (cylinder X 0 τ) u C)
    (hv : SchauderBound α (cylinder X τ T) v D)
    (hTrace : ∀ x ∈ X, u (x,τ) = v (x,τ))
    (htTrace : ∀ x ∈ X, timeD (cylinder X 0 τ) u (x,τ) = timeD (cylinder X τ T) v (x,τ)) :
    SchauderBound α (cylinder X 0 T) (timePaste τ u v) (2*(C+D)) := by
  have hC : C ≤ 2*(C+D) := by linarith [hu.2.1,hv.2.1]
  have hD : D ≤ 2*(C+D) := by linarith [hu.2.1,hv.2.1]
  have hSpatial := F05_physical_trace_spatial_jets hX u v τ
    (fun x hx => hu.1.2.2.2.2.1 (x,τ) ⟨hx,hτ.le,le_rfl⟩)
    (fun x hx => hv.1.2.2.2.2.1 (x,τ) ⟨hx,le_rfl,hT.le⟩) hTrace
  have hHess := holderBound_timePaste_space hα hu.2.2.2.1 hv.2.2.2.1
    (fun x hx => (hSpatial x hx).2)
  have hTime := holderBound_timePaste_space hα hu.2.2.2.2 hv.2.2.2.2 htTrace
  refine ⟨F05_c2_timePaste_physical hClosed hX hτ hT hu.1 hv.1 hTrace htTrace,
    by linarith [hu.2.1,hv.2.1],?_,?_,?_⟩
  · intro z hz
    rw [spatialD_timePaste]
    by_cases h : z.2 ≤ τ
    · simpa only [timePaste,ite_eq_left h] using
        And.intro (((hu.2.2.1 z ⟨hz.1,hz.2.1,h⟩).1).trans hC)
          (((hu.2.2.1 z ⟨hz.1,hz.2.1,h⟩).2).trans hC)
    · simpa only [timePaste,ite_eq_right h] using
        And.intro (((hv.2.2.1 z ⟨hz.1,le_of_not_ge h,hz.2.2⟩).1).trans hD)
          (((hv.2.2.1 z ⟨hz.1,le_of_not_ge h,hz.2.2⟩).2).trans hD)
  · simpa only [spatialDD_timePaste] using hHess
  · exact holderBound_congr_on hTime (fun z hz =>
      (timeD_timePaste_space hτ hT hu.1 hv.1 hTrace htTrace hz).symm)

end Yau.Proofs.F05Aux
