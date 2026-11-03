import Yau.Proofs.F01SpatialTensorClockJet
import Yau.Proofs.F01SlabSpatialTensorRegularity
import Yau.Proofs.F01SlabWordClockJets

/-! The actual scalar potential equation differentiates to the full
spatial tensor equation within the same original closed slab. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem slab_spatial_tensor_time_jet
    {f P : Point n → ℝ} {S : Set (Space n)} {I : Set ℝ}
    (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (hDense : ∀ t ∈ I, t ∈ closure (interior I))
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ I))
    (hP : ∀ t ∈ I, ContDiffOn ℝ ∞ (fun z => P (z, t)) S)
    (hJet : ∀ x ∈ S, ∀ t ∈ I, HasDerivWithinAt (fun s => f (x, s)) (P (x, t)) I t)
    (k : ℕ) {x : Space n} (hx : x ∈ S) {t : ℝ} (ht : t ∈ I) :
    HasDerivWithinAt (fun s => iteratedFDeriv ℝ k (fun z => f (z, s)) x)
      (iteratedFDeriv ℝ k (fun z => P (z, t)) x) I t := by
  have hCont : ContinuousWithinAt
      (fun s => iteratedFDeriv ℝ k (fun z => f (z, s)) x) I t :=
    ((slab_spatial_tensor_smooth hS hI hf k).continuousOn.comp
      (continuousOn_const.prodMk continuousOn_id) (fun s hs => ⟨hx, hs⟩)) t ht
  apply spatial_tensor_clock_jet_within_of_native_frame k _ _ ht hCont
  intro m
  let vs : List (Space n) := List.ofFn (fun i => realVec (m i))
  have hw := slab_spatial_word_time_jet hS hI hDense hf hJet vs x hx t ht
  have hTarget : spatialDerivativeWord vs P (x, t) =
      iteratedFDeriv ℝ k (fun z => P (z, t)) x (fun i => realVec (m i)) :=
    spatialDerivativeWord_ofFn_eq_iteratedFDeriv hS (hP t ht) k _ hx
  rw [hTarget] at hw
  apply hw.congr_of_mem _ ht
  intro s hs
  exact (spatialDerivativeWord_ofFn_eq_iteratedFDeriv hS
    (contDiffOn_space_slice hf hs) k (fun i => realVec (m i)) hx).symm

end Yau.NodeProofs.F01Aux
