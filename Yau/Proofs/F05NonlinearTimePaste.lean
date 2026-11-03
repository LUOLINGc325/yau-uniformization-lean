import Yau.Proofs.F05PhysicalTimePaste

/-! The original nonlinear equation itself supplies the joining time jet.
Thus actual equal physical traces glue to a genuine C2 solution without
an extra derivative-matching or restart-solver premise. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16BoundaryTimeAux
variable {n : ℕ}

theorem F05_nonlinear_timePaste_physical {X : Set (Space n)} (hClosed : IsClosed X)
    (hX : UniqueDiffOn ℝ X) {τ T : ℝ} (hτ : 0 < τ) (hT : τ < T)
    (u v : Point n → ℝ) (A : Point n → Mat n) (B : Point n → RIdx n → ℝ) (R : Point n → ℝ)
    (hu : C2 (cylinder X 0 τ) u) (hv : C2 (cylinder X τ T) v)
    (hTrace : ∀ x ∈ X, u (x,τ) = v (x,τ))
    (hUEq : ∀ z ∈ cylinder X 0 τ,
      timeD (cylinder X 0 τ) u z = Real.exp (-u z)*
        ((∑ i,∑ j,A z i j*spatialDD u z (realVec i) (realVec j))+
          ∑ i,B z i*spatialD u z (realVec i))+(1-Real.exp (-u z))*R z)
    (hVEq : ∀ z ∈ cylinder X τ T,
      timeD (cylinder X τ T) v z = Real.exp (-v z)*
        ((∑ i,∑ j,A z i j*spatialDD v z (realVec i) (realVec j))+
          ∑ i,B z i*spatialD v z (realVec i))+(1-Real.exp (-v z))*R z) :
    C2 (cylinder X 0 T) (timePaste τ u v) ∧
      ∀ z ∈ cylinder X 0 T,
        timeD (cylinder X 0 T) (timePaste τ u v) z = Real.exp (-timePaste τ u v z)*
          ((∑ i,∑ j,A z i j*spatialDD (timePaste τ u v) z (realVec i) (realVec j))+
            ∑ i,B z i*spatialD (timePaste τ u v) z (realVec i))+
              (1-Real.exp (-timePaste τ u v z))*R z := by
  have hSpatial := F05_physical_trace_spatial_jets hX u v τ
    (fun x hx => hu.2.2.2.2.1 (x,τ) ⟨hx,hτ.le,le_rfl⟩)
    (fun x hx => hv.2.2.2.2.1 (x,τ) ⟨hx,le_rfl,hT.le⟩) hTrace
  have htTrace : ∀ x ∈ X, timeD (cylinder X 0 τ) u (x,τ) = timeD (cylinder X τ T) v (x,τ) := by
    intro x hx
    rw [hUEq (x,τ) ⟨hx,hτ.le,le_rfl⟩,hVEq (x,τ) ⟨hx,le_rfl,hT.le⟩,
      hTrace x hx,(hSpatial x hx).1,(hSpatial x hx).2]
  refine ⟨F05_c2_timePaste_physical hClosed hX hτ hT hu hv hTrace htTrace,?_⟩
  intro z hz
  rw [timeD_timePaste_space hτ hT hu hv hTrace htTrace hz,spatialD_timePaste,spatialDD_timePaste]
  by_cases h : z.2 ≤ τ
  · simpa only [timePaste,ite_eq_left h] using hUEq z ⟨hz.1,hz.2.1,h⟩
  · simpa only [timePaste,ite_eq_right h] using hVEq z ⟨hz.1,le_of_not_ge h,hz.2.2⟩

end Yau.Proofs.F05Aux
