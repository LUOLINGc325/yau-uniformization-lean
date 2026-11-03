import Yau.Proofs.F01ClosedSpatialSecondJet

/-! Uniform convergence of actual joint second jets gives convergence
of the computed spatial real Hessian on the original closed time slab. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem closed_spatial_second_limit_of_jets
    {S : Set E} {I : Set ℝ} (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (f : ℕ → E × ℝ → F) (g : E × ℝ → F)
    (hf : ∀ m, ContDiffOn ℝ ∞ (f m) (S ×ˢ I)) (hg : ContDiffOn ℝ ∞ g (S ×ˢ I))
    (hconv : TendstoUniformlyOn (fun m p => iteratedFDerivWithin ℝ 2 (f m) (S ×ˢ I) p)
      (iteratedFDerivWithin ℝ 2 g (S ×ˢ I)) atTop (S ×ˢ I))
    {x : E} (hx : x ∈ S) {t : ℝ} (ht : t ∈ I) (v w : E) :
    Tendsto (fun m => fderiv ℝ (fderiv ℝ (fun z => f m (z, t))) x v w) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ (fun z => g (z, t))) x v w)) := by
  have hU : UniqueDiffOn ℝ (S ×ˢ I) := hS.uniqueDiffOn.prod hI
  have hEval : Continuous (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E × ℝ) F =>
      D ![(v, 0), (w, 0)]) := by fun_prop
  have hpoint := hconv.tendsto_at (show (x, t) ∈ S ×ˢ I from ⟨hx, ht⟩)
  have heval := hEval.continuousAt.tendsto.comp hpoint
  have heq (q : E × ℝ → F) (hq : ContDiffOn ℝ ∞ q (S ×ˢ I)) :
      fderiv ℝ (fderiv ℝ (fun z => q (z, t))) x v w =
        iteratedFDerivWithin ℝ 2 q (S ×ˢ I) (x, t) ![(v, 0), (w, 0)] := by
    rw [iteratedFDerivWithin_two_apply' q hU ⟨hx, ht⟩ (v, 0) (w, 0)]
    exact spatial_second_deriv_eq_closed_joint_second hS hI hq hx ht v w
  have hseq : (fun m => fderiv ℝ (fderiv ℝ (fun z => f m (z, t))) x v w) =
      fun m => iteratedFDerivWithin ℝ 2 (f m) (S ×ˢ I) (x, t) ![(v, 0), (w, 0)] :=
    funext (fun m => heq (f m) (hf m))
  rw [hseq, heq g hg]
  exact heval

end Yau.NodeProofs.F01Aux
