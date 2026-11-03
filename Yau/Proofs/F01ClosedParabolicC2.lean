import Yau.Proofs.F01ClosedSpatialDerivative
import Yau.Proofs.F01ClosedTimeDerivative
import Yau.Proofs.F01ClosedTimeSlices

/-! Actual joint smoothness on a closed slab gives the original
parabolic C² predicate with its computed spatial and one-sided time jets. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem closed_slab_parabolic_C2 {F : Point n → ℝ} {S : Set (Space n)} {I : Set ℝ}
    (hS : IsOpen S) (hI : UniqueDiffOn ℝ I) (hF : ContDiffOn ℝ ∞ F (S ×ˢ I)) :
    C2 (S ×ˢ I) F := by
  have hD := closed_slab_space_fderiv_smooth hS hI hF
  have hDD := closed_slab_space_fderiv_smooth hS hI hD
  have hset (p : Point n) (hp : p ∈ S ×ˢ I) : {t : ℝ | (p.1, t) ∈ S ×ˢ I} = I := by
    ext t
    exact and_iff_right hp.1
  have htime : ContinuousOn (timeD (S ×ˢ I) F) (S ×ˢ I) := by
    apply (closed_slab_time_derivWithin_smooth hS hI hF).continuousOn.congr
    intro p hp
    unfold timeD
    rw [hset p hp]
  refine ⟨hF.continuousOn, hD.continuousOn, hDD.continuousOn, htime, ?_, ?_⟩
  · intro p hp
    exact (closed_slab_slice_jets hF hS hp.1 hp.2).1
  · intro p hp
    rw [hset p hp]
    exact (closed_slab_slice_jets hF hS hp.1 hp.2).2

end Yau.NodeProofs.F01Aux
