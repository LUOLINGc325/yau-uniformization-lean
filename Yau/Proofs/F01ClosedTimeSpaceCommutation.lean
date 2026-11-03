import Yau.Proofs.F01ClosedTimeDerivative
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Spatial and actual one-sided temporal derivatives commute on both
closed slab faces. Symmetry is proved within the same slab, using its
interior density; no jointly smooth extension of the zero extension is used. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem closed_time_space_derivative_commute {f : E × ℝ → F} {S : Set E} {T : ℝ}
    (hS : IsOpen S) (hT : 0 < T) (hf : ContDiffOn ℝ ∞ f (S ×ˢ Icc 0 T))
    {x : E} (hx : x ∈ S) {t : ℝ} (ht : t ∈ Icc 0 T) (v : E) :
    derivWithin (fun s => fderiv ℝ (fun z => f (z, s)) x v) (Icc 0 T) t =
      fderiv ℝ (fun z => derivWithin (fun s => f (z, s)) (Icc 0 T) t) x v := by
  let Q := S ×ˢ Icc 0 T
  let J := fderivWithin ℝ f Q
  let G := fun p : E × ℝ => fderiv ℝ (fun z => f (z, p.2)) p.1 v
  let P := fun p : E × ℝ => derivWithin (fun s => f (p.1, s)) (Icc 0 T) p.2
  have hI := uniqueDiffOn_Icc hT
  have hQ : UniqueDiffOn ℝ Q := hS.uniqueDiffOn.prod hI
  have hp : (x, t) ∈ Q := ⟨hx, ht⟩
  have hJ : ContDiffOn ℝ ∞ J Q := hf.fderivWithin hQ (m := ∞) (by simp)
  have hG : ContDiffOn ℝ ∞ G Q := closed_slab_space_direction_smooth hS hI hf v
  have hP : ContDiffOn ℝ ∞ P Q := closed_slab_time_derivWithin_smooth hS hI hf
  have hGeq : EqOn G (fun p => J p (v, 0)) Q := by
    intro p hp
    have he := congrArg (fun D : E →L[ℝ] F => D v)
      (space_fderiv_eq_joint_within hS (hf.differentiableOn (by simp)) hp.1 hp.2)
    exact he
  have hPeq : EqOn P (fun p => J p (0, 1)) Q :=
    fun p hp => time_derivWithin_eq_joint_within hI (hf.differentiableOn (by simp)) hp.1 hp.2
  have hGderiv : fderivWithin ℝ G Q (x, t) (0, 1) =
      fderivWithin ℝ J Q (x, t) (0, 1) (v, 0) := by
    rw [fderivWithin_congr hGeq (hGeq hp),
      fderivWithin_clm_apply (hQ _ hp) ((hJ.differentiableOn (by simp)) _ hp)
        (differentiableWithinAt_const (c := (v, 0)))]
    simp only [fderivWithin_const_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  have hPderiv : fderivWithin ℝ P Q (x, t) (v, 0) =
      fderivWithin ℝ J Q (x, t) (v, 0) (0, 1) := by
    rw [fderivWithin_congr hPeq (hPeq hp),
      fderivWithin_clm_apply (hQ _ hp) ((hJ.differentiableOn (by simp)) _ hp)
        (differentiableWithinAt_const (c := ((0 : E), (1 : ℝ))))]
    simp only [fderivWithin_const_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  have hclosure : (x, t) ∈ closure (interior Q) := by
    change (x, t) ∈ closure (interior (S ×ˢ Icc 0 T))
    rw [interior_prod_eq, hS.interior_eq, interior_Icc, closure_prod_eq, closure_Ioo (ne_of_lt hT)]
    exact ⟨subset_closure hx, ht⟩
  have hsym := (hf (x, t) hp).isSymmSndFDerivWithinAt (by simp) hQ hclosure hp
  change derivWithin (fun s => G (x, s)) (Icc 0 T) t = fderiv ℝ (fun z => P (z, t)) x v
  rw [time_derivWithin_eq_joint_within hI (hG.differentiableOn (by simp)) hx ht,
    space_fderiv_eq_joint_within hS (hP.differentiableOn (by simp)) hx ht]
  change fderivWithin ℝ G Q (x, t) (0, 1) = fderivWithin ℝ P Q (x, t) (v, 0)
  rw [hGderiv, hPderiv]
  exact hsym (0, 1) (v, 0)

end Yau.NodeProofs.F01Aux
