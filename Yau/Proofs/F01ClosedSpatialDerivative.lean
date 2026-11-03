import spec.CHAIN.CONTRACTS

/-! Spatial differentiation preserves joint smoothness on an open spatial
domain times the original closed time domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem space_fderiv_eq_joint_within {f : E × ℝ → F}
    {S : Set E} {I : Set ℝ} (hS : IsOpen S)
    (hf : DifferentiableOn ℝ f (S ×ˢ I)) {x : E} (hx : x ∈ S)
    {t : ℝ} (ht : t ∈ I) :
    fderiv ℝ (fun z => f (z, t)) x =
      (fderivWithin ℝ f (S ×ˢ I) (x, t)).comp
        ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) := by
  have hpair : HasFDerivAt (fun z : E => (z, t))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  have hm : MapsTo (fun z : E => (z, t)) S (S ×ˢ I) := fun z hz => ⟨hz, ht⟩
  have h : HasFDerivWithinAt (fun z => f (z, t))
      ((fderivWithin ℝ f (S ×ˢ I) (x, t)).comp
        ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ))) S x :=
    (hf (x, t) ⟨hx, ht⟩).hasFDerivWithinAt.comp x
      hpair.hasFDerivWithinAt hm
  exact (h.hasFDerivAt (hS.mem_nhds hx)).fderiv

theorem closed_slab_space_fderiv_smooth {f : E × ℝ → F}
    {S : Set E} {I : Set ℝ} (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ I)) :
    ContDiffOn ℝ ∞ (fun p : E × ℝ => fderiv ℝ (fun z => f (z, p.2)) p.1)
      (S ×ˢ I) := by
  have hdf := hf.fderivWithin (hS.uniqueDiffOn.prod hI) (m := ∞) (by simp)
  have hcomp := hdf.clm_comp (contDiffOn_const
    (c := (ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)))
  apply hcomp.congr
  intro p hp
  exact space_fderiv_eq_joint_within hS (hf.differentiableOn (by simp)) hp.1 hp.2

theorem closed_slab_space_direction_smooth {f : E × ℝ → F}
    {S : Set E} {I : Set ℝ} (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ I)) (v : E) :
    ContDiffOn ℝ ∞ (fun p : E × ℝ => fderiv ℝ (fun z => f (z, p.2)) p.1 v)
      (S ×ˢ I) :=
  (closed_slab_space_fderiv_smooth hS hI hf).clm_apply contDiffOn_const

end Yau.NodeProofs.F01Aux
