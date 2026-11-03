import Yau.Proofs.F01ClosedTimeDerivative
import Yau.Proofs.F01ClosedSpatialSecondJet

/-! The second one-sided clock derivative is an evaluation of the
actual joint second within-jet. Thus the common compactness subsequence
also carries the scalar time-derivative cap through both closed faces. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem closed_second_clock_derivative_eq_joint_second
    {f : E × ℝ → F} {S : Set E} {I : Set ℝ}
    (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ I))
    {x : E} (hx : x ∈ S) {t : ℝ} (ht : t ∈ I) :
    derivWithin (fun s => derivWithin (fun τ => f (x,τ)) I s) I t =
      iteratedFDerivWithin ℝ 2 f (S ×ˢ I) (x,t) ![(0,1),(0,1)] := by
  let V : E × ℝ → F := fun p => fderivWithin ℝ f (S ×ˢ I) p (0,1)
  have hUnique : UniqueDiffOn ℝ (S ×ˢ I) := hS.uniqueDiffOn.prod hI
  have hdf : ContDiffOn ℝ ∞ (fderivWithin ℝ f (S ×ˢ I)) (S ×ˢ I) :=
    hf.fderivWithin hUnique (m := ∞) (by simp)
  have hV : ContDiffOn ℝ ∞ V (S ×ˢ I) := hdf.clm_apply contDiffOn_const
  have heq : (fun s => derivWithin (fun τ => f (x,τ)) I s) =ᶠ[𝓝[I] t]
      (fun s => V (x,s)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact time_derivWithin_eq_joint_within hI (hf.differentiableOn (by simp)) hx hs
  rw [heq.derivWithin_eq_of_mem ht,
    time_derivWithin_eq_joint_within hI (hV.differentiableOn (by simp)) hx ht]
  have hderivV : fderivWithin ℝ V (S ×ˢ I) (x,t) (0,1) =
      fderivWithin ℝ (fderivWithin ℝ f (S ×ˢ I)) (S ×ˢ I) (x,t) (0,1) (0,1) := by
    dsimp only [V]
    rw [fderivWithin_clm_apply (hUnique (x,t) ⟨hx,ht⟩)
      (hdf.differentiableOn (by simp) (x,t) ⟨hx,ht⟩)
      (differentiableWithinAt_const ((0 : E),(1 : ℝ)))]
    simp
  rw [hderivV, iteratedFDerivWithin_two_apply' f hUnique ⟨hx,ht⟩]

theorem eventual_closed_second_clock_derivative_limit_of_jets
    {S : Set E} {I : Set ℝ} (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (f : ℕ → E × ℝ → F) (g : E × ℝ → F)
    (hf : ∀ᶠ m in atTop, ContDiffOn ℝ ∞ (f m) (S ×ˢ I))
    (hg : ContDiffOn ℝ ∞ g (S ×ˢ I))
    (hconv : TendstoUniformlyOn
      (fun m p => iteratedFDerivWithin ℝ 2 (f m) (S ×ˢ I) p)
      (iteratedFDerivWithin ℝ 2 g (S ×ˢ I)) atTop (S ×ˢ I))
    {x : E} (hx : x ∈ S) {t : ℝ} (ht : t ∈ I) :
    Tendsto (fun m => derivWithin (fun s => derivWithin (fun τ => f m (x,τ)) I s) I t)
      atTop (𝓝 (derivWithin (fun s => derivWithin (fun τ => g (x,τ)) I s) I t)) := by
  have hEval : Continuous
      (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E × ℝ) F => D ![(0,1),(0,1)]) := by
    fun_prop
  have hLimit := hEval.continuousAt.tendsto.comp
    (hconv.tendsto_at (show (x,t) ∈ S ×ˢ I from ⟨hx,ht⟩))
  rw [← closed_second_clock_derivative_eq_joint_second hS hI hg hx ht] at hLimit
  exact hLimit.congr' (hf.mono (fun m hm =>
    (closed_second_clock_derivative_eq_joint_second hS hI hm hx ht).symm))

end Yau.NodeProofs.F01Aux
