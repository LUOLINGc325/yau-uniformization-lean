import Yau.Proofs.F01ProductTensorHolder

/-! The finite jet of three fields is assembled in the native product
norm with one common budget, fixed before all three realizations. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {F G H : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem holderBound_spatial_tensor_triple {Q : Set (Point n)} {O : Set (Space n)}
    {β C : ℝ} {f : Point n → F} {g : Point n → G} {h : Point n → H}
    (k : ℕ) (hO : IsOpen O) (hQ : Q ⊆ O ×ˢ (Set.univ : Set ℝ))
    (hfs : ∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => f (z, p.2)) O)
    (hgs : ∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => g (z, p.2)) O)
    (hhs : ∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => h (z, p.2)) O)
    (hf : HolderBound β Q (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1) C)
    (hg : HolderBound β Q (fun p => iteratedFDeriv ℝ k (fun z => g (z, p.2)) p.1) C)
    (hh : HolderBound β Q (fun p => iteratedFDeriv ℝ k (fun z => h (z, p.2)) p.1) C) :
    HolderBound β Q (fun p => iteratedFDeriv ℝ k
      (fun z => (f (z, p.2), (g (z, p.2), h (z, p.2)))) p.1) C := by
  have hPair : HolderBound β Q (fun p => iteratedFDeriv ℝ k
      (fun z => (g (z, p.2), h (z, p.2))) p.1) C := by
    simpa only [max_self] using holderBound_spatial_tensor_pair
      (F := G) (G := H) (f := g) (g := h) (C := C) (D := C) k hO hQ hgs hhs hg hh
  have hPairSmooth (p : Point n) (hp : p ∈ Q) :
      ContDiffOn ℝ ∞ (fun z => (g (z, p.2), h (z, p.2))) O :=
    (hgs p hp).prodMk (hhs p hp)
  simpa only [max_self] using
    holderBound_spatial_tensor_pair (F := F) (G := G × H)
      (f := f) (g := fun p => (g p, h p)) (C := C) (D := C)
      k hO hQ hfs hPairSmooth hf hPair

end Yau.NodeProofs.F01Aux
