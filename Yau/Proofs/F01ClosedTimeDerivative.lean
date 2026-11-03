import Yau.Proofs.F01ClosedSpatialDerivative

/-! The actual one-sided time derivative is a jointly smooth scalar on
the same closed slab, rather than a derivative of an assumed extension. -/
noncomputable section
open Set
open scoped ContDiff Manifold
namespace Yau.NodeProofs.F01Aux
open Yau
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem time_derivWithin_eq_joint_within {f : E × ℝ → F}
    {S : Set E} {I : Set ℝ} (hI : UniqueDiffOn ℝ I)
    (hf : DifferentiableOn ℝ f (S ×ˢ I)) {x : E} (hx : x ∈ S)
    {t : ℝ} (ht : t ∈ I) :
    derivWithin (fun s => f (x, s)) I t =
      fderivWithin ℝ f (S ×ˢ I) (x, t) (0, 1) := by
  have hpair : HasDerivWithinAt (fun s : ℝ => (x, s)) (0, 1) I t :=
    (hasDerivWithinAt_const t I x).prodMk (hasDerivAt_id t).hasDerivWithinAt
  have hm : MapsTo (fun s : ℝ => (x, s)) I (S ×ˢ I) := fun s hs => ⟨hx, hs⟩
  exact ((hf (x, t) ⟨hx, ht⟩).hasFDerivWithinAt.comp_hasDerivWithinAt t hpair hm).derivWithin
    (hI t ht)

theorem closed_slab_time_derivWithin_smooth {f : E × ℝ → F}
    {S : Set E} {I : Set ℝ} (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ I)) :
    ContDiffOn ℝ ∞ (fun p : E × ℝ => derivWithin (fun s => f (p.1, s)) I p.2)
      (S ×ˢ I) := by
  have hdf := hf.fderivWithin (hS.uniqueDiffOn.prod hI) (m := ∞) (by simp)
  have heval := hdf.clm_apply (contDiffOn_const (c := ((0 : E), (1 : ℝ))))
  apply heval.congr
  intro p hp
  exact time_derivWithin_eq_joint_within hI (hf.differentiableOn (by simp)) hp.1 hp.2

theorem smoothSpaceTime_time_derivWithin {n : ℕ} {M : ComplexManifold n}
    {F : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hF : SmoothSpaceTime F I) (hI : UniqueDiffOn ℝ I) :
    SmoothSpaceTime (fun x t => derivWithin (F x) I t) I := by
  intro a
  exact closed_slab_time_derivWithin_smooth
    (isOpen_extChartAt_target (I := ComplexModel n) a) hI (hF a)

end Yau.NodeProofs.F01Aux
