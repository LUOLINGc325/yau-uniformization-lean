import Yau.Proofs.F01ZeroExtendedSpatialWords

/-! Every spatial word of the genuine zero-extended potential retains
its computed zero-extended first time jet. The proof glues actual
one-sided jets; it assumes no joint higher time extension. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem zero_extended_spatial_words_time_jet {u P : E × ℝ → F} {S : Set E} {a T : ℝ}
    (hS : IsOpen S) (hT : 0 < T) (hu : ContDiffOn ℝ ∞ u (S ×ˢ Icc 0 T))
    (hu0 : ∀ x ∈ S, u (x, 0) = 0) (hP0 : ∀ x ∈ S, P (x, 0) = 0)
    (hJet : ∀ x ∈ S, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => u (x, s)) (P (x, t)) (Icc 0 T) t)
    (vs : List E) {x : E} (hx : x ∈ S) {t : ℝ} (ht : t ∈ Icc a T) :
    HasDerivWithinAt (fun s => spatialDerivativeWord vs (forwardZeroSpaceTime u) (x, s))
      (spatialDerivativeWord vs (forwardZeroSpaceTime P) (x, t)) (Icc a T) t := by
  simp only [spatialDerivativeWord_forwardZeroSpaceTime]
  exact forwardZeroExtension_time_jet hT
    (spatialDerivativeWord_initial_zero hS hu0 vs x hx)
    (spatialDerivativeWord_initial_zero hS hP0 vs x hx)
    (spatialDerivativeWord_time_jet hS hT hu hJet vs x hx) ht

end Yau.NodeProofs.F01Aux
