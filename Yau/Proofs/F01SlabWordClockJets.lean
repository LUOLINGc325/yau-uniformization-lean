import Yau.Proofs.F01ClosedTimeSpaceCommutation
import Yau.Proofs.F01SpatialDerivativeWords

/-! Genuine clock-space commutation on any closed interval with dense
interior. This keeps both time faces in shifted positive-time patches;
no extension across either face is assumed. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem slab_time_space_derivative_commute {f : E × ℝ → F} {S : Set E} {I : Set ℝ}
    (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (hDense : ∀ t ∈ I, t ∈ closure (interior I)) (hf : ContDiffOn ℝ ∞ f (S ×ˢ I))
    {x : E} (hx : x ∈ S) {t : ℝ} (ht : t ∈ I) (v : E) :
    derivWithin (fun s => fderiv ℝ (fun z => f (z, s)) x v) (I) t =
      fderiv ℝ (fun z => derivWithin (fun s => f (z, s)) (I) t) x v := by
  let Q := S ×ˢ I
  let J := fderivWithin ℝ f Q
  let G := fun p : E × ℝ => fderiv ℝ (fun z => f (z, p.2)) p.1 v
  let P := fun p : E × ℝ => derivWithin (fun s => f (p.1, s)) (I) p.2
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
    change (x, t) ∈ closure (interior (S ×ˢ I))
    rw [interior_prod_eq, hS.interior_eq, closure_prod_eq]
    exact ⟨subset_closure hx, hDense t ht⟩
  have hsym := (hf (x, t) hp).isSymmSndFDerivWithinAt (by simp) hQ hclosure hp
  change derivWithin (fun s => G (x, s)) (I) t = fderiv ℝ (fun z => P (z, t)) x v
  rw [time_derivWithin_eq_joint_within hI (hG.differentiableOn (by simp)) hx ht,
    space_fderiv_eq_joint_within hS (hP.differentiableOn (by simp)) hx ht]
  change fderivWithin ℝ G Q (x, t) (0, 1) = fderivWithin ℝ P Q (x, t) (v, 0)
  rw [hGderiv, hPderiv]
  exact hsym (0, 1) (v, 0)


theorem slab_space_direction_time_jet {f P : E × ℝ → F} {S : Set E} {I : Set ℝ}
    (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (hDense : ∀ t ∈ I, t ∈ closure (interior I))
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ I))
    (hJet : ∀ x ∈ S, ∀ t ∈ I, HasDerivWithinAt (fun s => f (x, s)) (P (x, t)) I t)
    {x : E} (hx : x ∈ S) {t : ℝ} (ht : t ∈ I) (v : E) :
    HasDerivWithinAt (fun s => fderiv ℝ (fun z => f (z, s)) x v)
      (fderiv ℝ (fun z => P (z, t)) x v) I t := by
  have hG := closed_slab_space_direction_smooth hS hI hf v
  have hcurve : ContDiffOn ℝ ∞ (fun s => fderiv ℝ (fun z => f (z, s)) x v) I :=
    hG.comp (contDiffOn_const.prodMk contDiffOn_id) (fun s hs => ⟨hx, hs⟩)
  have hd := (hcurve t ht).differentiableWithinAt (by simp) |>.hasDerivWithinAt
  have heq : (fun z => derivWithin (fun s => f (z, s)) I t) =ᶠ[𝓝 x] (fun z => P (z, t)) := by
    filter_upwards [hS.mem_nhds hx] with z hz
    exact (hJet z hz t ht).derivWithin (hI t ht)
  have he := slab_time_space_derivative_commute hS hI hDense hf hx ht v
  rw [heq.fderiv_eq] at he
  rw [he] at hd
  exact hd

theorem slab_spatialDerivativeWord_smooth {f : E × ℝ → F} {S : Set E} {I : Set ℝ}
    (hS : IsOpen S) (hI : UniqueDiffOn ℝ I) (hf : ContDiffOn ℝ ∞ f (S ×ˢ I))
    (vs : List E) : ContDiffOn ℝ ∞ (spatialDerivativeWord vs f) (S ×ˢ I) := by
  induction vs with
  | nil => exact hf
  | cons v vs ih => exact closed_slab_space_direction_smooth hS hI ih v

theorem slab_spatial_word_time_jet {f P : E × ℝ → F} {S : Set E} {I : Set ℝ}
    (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (hDense : ∀ t ∈ I, t ∈ closure (interior I))
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ I))
    (hJet : ∀ x ∈ S, ∀ t ∈ I, HasDerivWithinAt (fun s => f (x, s)) (P (x, t)) I t)
    (vs : List E) : ∀ x ∈ S, ∀ t ∈ I,
      HasDerivWithinAt (fun s => spatialDerivativeWord vs f (x, s))
        (spatialDerivativeWord vs P (x, t)) I t := by
  induction vs with
  | nil => exact hJet
  | cons v vs ih =>
    intro x hx t ht
    exact slab_space_direction_time_jet hS hI hDense
      (slab_spatialDerivativeWord_smooth hS hI hf vs) ih hx ht v

end Yau.NodeProofs.F01Aux
