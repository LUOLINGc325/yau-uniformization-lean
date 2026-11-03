import Yau.Proofs.F01ClosedSpatialDerivative
import Yau.Proofs.F01CylinderJetRestriction

/-! Spatial second derivatives are actual evaluations of the joint
closed-cylinder second derivative, including both closed time faces. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem spatial_second_deriv_eq_closed_joint_second
    {f : E × ℝ → F} {S : Set E} {I : Set ℝ}
    (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ I)) {x : E} (hx : x ∈ S)
    {t : ℝ} (ht : t ∈ I) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun z => f (z, t))) x v w =
      fderivWithin ℝ (fderivWithin ℝ f (S ×ˢ I)) (S ×ˢ I) (x, t) (v, 0) (w, 0) := by
  let G : E × ℝ → F := fun p => fderivWithin ℝ f (S ×ˢ I) p (w, 0)
  have hU : UniqueDiffOn ℝ (S ×ˢ I) := hS.uniqueDiffOn.prod hI
  have hdf : ContDiffOn ℝ ∞ (fderivWithin ℝ f (S ×ˢ I)) (S ×ˢ I) :=
    hf.fderivWithin hU (m := ∞) (by simp)
  have hG : ContDiffOn ℝ ∞ G (S ×ˢ I) := hdf.clm_apply contDiffOn_const
  have hslice : ContDiffOn ℝ ∞ (fun z => f (z, t)) S :=
    hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)
  have hslice2 : ContDiffAt ℝ 2 (fun z => f (z, t)) x :=
    (hslice.contDiffAt (hS.mem_nhds hx)).of_le (by simp)
  have hds : DifferentiableAt ℝ (fderiv ℝ (fun z => f (z, t))) x :=
    (hslice2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heq : (fun y => fderiv ℝ (fun z => f (z, t)) y w) =ᶠ[𝓝 x]
      (fun y => G (y, t)) := by
    filter_upwards [hS.mem_nhds hx] with y hy
    rw [space_fderiv_eq_joint_within hS (hf.differentiableOn (by simp)) hy ht]
    simp only [G, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, zero_apply]
  have hspaceG := congrArg (fun D : E →L[ℝ] F => D v)
    (space_fderiv_eq_joint_within hS (hG.differentiableOn (by simp)) hx ht)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply] at hspaceG
  have hderivG : fderivWithin ℝ G (S ×ˢ I) (x, t) (v, 0) =
      fderivWithin ℝ (fderivWithin ℝ f (S ×ˢ I)) (S ×ˢ I) (x, t) (v, 0) (w, 0) := by
    dsimp only [G]
    rw [fderivWithin_clm_apply (hU (x, t) ⟨hx, ht⟩)
      (hdf.differentiableOn (by simp) (x, t) ⟨hx, ht⟩) (differentiableWithinAt_const (w, (0 : ℝ)))]
    simp
  calc
    _ = fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, t)) y w) x v := by
      have he := fderiv_clm_apply hds (differentiableAt_const w)
      simpa using (congrArg (fun D : E →L[ℝ] F => D v) he).symm
    _ = fderiv ℝ (fun y => G (y, t)) x v := congrArg (fun D : E →L[ℝ] F => D v) heq.fderiv_eq
    _ = _ := hspaceG.trans hderivG

end Yau.NodeProofs.F01Aux
