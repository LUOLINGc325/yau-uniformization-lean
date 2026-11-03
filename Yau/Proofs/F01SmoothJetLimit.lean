import Yau.Proofs.F01ConvexJetLimit

/-! Uniform limits of the actual complete derivative tower on a convex
closed domain give a genuine smooth function and its actual derivatives.
The original closed time faces remain in the domain throughout. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smooth_closed_jet_limit
    {S : Set E} (hS : Convex ℝ S) (hUnique : UniqueDiffOn ℝ S)
    (f : ℕ → E → F) (hf : ∀ m, ContDiffOn ℝ ∞ (f m) S)
    (q : E → FormalMultilinearSeries ℝ E F)
    (huniform : ∀ k : ℕ, TendstoUniformlyOn
      (fun m x => iteratedFDerivWithin ℝ k (f m) S x) (fun x => q x k) atTop S) :
    ContDiffOn ℝ ∞ (fun x => (q x 0).curry0) S ∧
      ∀ k x, x ∈ S → q x k =
        iteratedFDerivWithin ℝ k (fun y => (q y 0).curry0) S x := by
  have hTaylorSeq (m : ℕ) : HasFTaylorSeriesUpToOn ∞ (f m)
      (ftaylorSeriesWithin ℝ (f m) S) S := (hf m).ftaylorSeriesWithin hUnique
  have hcont (k : ℕ) : ContinuousOn (fun x => q x k) S :=
    (huniform k).continuousOn (Filter.Frequently.of_forall
      (fun m => (hTaylorSeq m).cont k (by simp)))
  have hTaylor : HasFTaylorSeriesUpToOn ∞ (fun x => (q x 0).curry0) q S := by
    refine ⟨(fun _ _ => rfl), ?_, (fun k _ => hcont k)⟩
    intro k hk x hx
    let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F
    have hcurry : UniformContinuous
        (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) F => A.curryLeft) :=
      curry.isometry.uniformContinuous
    have hDerivUniform : TendstoUniformlyOn
        (fun m y => (iteratedFDerivWithin ℝ (k + 1) (f m) S y).curryLeft)
        (fun y => (q y (k + 1)).curryLeft) atTop S := by
      simpa only [Function.comp_def] using hcurry.comp_tendstoUniformlyOn (huniform (k + 1))
    apply hasFDerivWithinAt_of_uniform_jet_limit hS
      (fun m y => iteratedFDerivWithin ℝ k (f m) S y)
      (fun m y => (iteratedFDerivWithin ℝ (k + 1) (f m) S y).curryLeft)
      (fun y => q y k) (fun y => (q y (k + 1)).curryLeft)
      (fun m y hy => (hTaylorSeq m).fderivWithin k hk y hy)
      (fun y hy => (huniform k).tendsto_at hy) hDerivUniform
      (hcurry.continuous.comp_continuousOn (hcont (k + 1))) hx
  refine ⟨hTaylor.contDiffOn, ?_⟩
  intro k x hx
  exact hTaylor.eq_iteratedFDerivWithin_of_uniqueDiffOn (by simp) hUnique hx

end Yau.NodeProofs.F01Aux
