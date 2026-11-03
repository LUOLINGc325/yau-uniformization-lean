import Yau.Proofs.F01SpatialWordsTensorJets

/-! The zeroth native tensor jet is the original value, isometrically.
Its Holder estimate therefore needs no differentiability premise. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem holderBound_from_zero_spatial_jet {Q : Set (Point n)} {β C : ℝ} {f : Point n → F}
    (hf : HolderBound β Q (fun p => iteratedFDeriv ℝ 0 (fun z => f (z, p.2)) p.1) C) :
    HolderBound β Q f C := by
  refine ⟨hf.1, ?_, ?_⟩
  · intro p hp
    simpa only [norm_iteratedFDeriv_zero] using hf.2.1 p hp
  · intro p hp q hq
    let J := (continuousMultilinearCurryFin0 ℝ (Space n) F).symm
    have hh := hf.2.2 p hp q hq
    change ‖J (f p) - J (f q)‖ ≤ _ at hh
    rw [← dist_eq_norm, J.isometry.dist_eq, dist_eq_norm] at hh
    exact hh

end Yau.NodeProofs.F01Aux
