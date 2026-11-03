import Yau.Proofs.F01ClosedSpatialDerivative

/-! All actual spatial Frechet jets are jointly smooth within the
original slab. Its time faces are retained throughout differentiation. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem slab_spatial_tensor_smooth
    {f : E × ℝ → F} {S : Set E} {I : Set ℝ}
    (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ I)) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p => iteratedFDeriv ℝ k (fun x => f (x, p.2)) p.1) (S ×ˢ I) := by
  induction k with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp_contDiffOn hf
  | succ k ih =>
    let L : (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) F :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff.comp_contDiffOn (closed_slab_space_fderiv_smooth hS hI ih)

end Yau.NodeProofs.F01Aux
