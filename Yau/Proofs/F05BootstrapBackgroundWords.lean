import Yau.Proofs.F05SmoothSpatialJets
import Yau.Proofs.F05BootstrapGoodDirections

/-! Actual good words of a smooth fixed background remain smooth on the
same positive closed-time cylinder. This does not concern the unknown
solution or assume smoothness of its exponential coefficient. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_joint_vector_time_derivative_smooth {U : Set (Space n)} {I : Set ℝ}
    (hI : UniqueDiffOn ℝ I) {f : Point n → V} (hf : ContDiffOn ℝ ∞ f (U ×ˢ I)) :
    ContDiffOn ℝ ∞ (fun p => derivWithin (fun t => f (p.1,t)) I p.2) (U ×ˢ I) := by
  let Q := U ×ˢ I
  have hJoint : ContDiffOn ℝ ∞ (fun q : Point n × ℝ => f (q.1.1,q.2)) (Q ×ˢ I) :=
    hf.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd) (fun q hq => ⟨hq.1.1,hq.2⟩)
  have hWithin : ContDiffOn ℝ ∞
      (fun p : Point n => fderivWithin ℝ (fun t => f (p.1,t)) I p.2) Q := by
    intro p hp
    have hJ : ContDiffWithinAt ℝ ∞
        (Function.uncurry (fun (q : Point n) (t : ℝ) => f (q.1,t))) (Q ×ˢ I) (p,p.2) :=
      hJoint (p,p.2) ⟨hp,hp.2⟩
    exact hJ.fderivWithin (m := ∞) contDiffWithinAt_snd hI (by simp) hp (fun q hq => hq.2)
  simpa only [derivWithin] using hWithin.clm_apply
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Point n => (1 : ℝ)) Q)

theorem F05_smooth_background_good_partial {U : Set (Space n)} (hU : IsOpen U) {T : ℝ}
    {f : Point n → V} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Ioc 0 T)) (d : Option (RIdx n)) :
    ContDiffOn ℝ ∞ (F05GoodPartial T d f) (U ×ˢ Ioc 0 T) := by
  cases d with
  | none => exact F05_joint_vector_time_derivative_smooth (uniqueDiffOn_Ioc 0 T) hf
  | some k =>
    have hSpatial := F05_joint_spatial_derivative_smooth hU hf
    have hSmooth := hSpatial.clm_apply
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Point n => realVec k) (U ×ˢ Ioc 0 T))
    apply hSmooth.congr
    intro p hp
    have hSlice : ContDiffOn ℝ ∞ (fun x => f (x,p.2)) U :=
      hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => ⟨hx,hp.2⟩)
    have hDiff : DifferentiableAt ℝ (fun x => f (x,p.2)) p.1 :=
      (hSlice.differentiableOn (by simp) p.1 hp.1).differentiableAt (hU.mem_nhds hp.1)
    have hLine : HasDerivAt (fun a : ℝ => p.1+a • realVec k) (realVec k) 0 := by
      simpa only [id_eq,one_smul] using
        ((hasDerivAt_id (0 : ℝ)).smul_const (realVec k)).const_add p.1
    simpa only [F05GoodPartial,Function.comp_def,zero_smul,add_zero] using
      (hDiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hLine (by simp)).deriv

theorem F05_smooth_background_good_words {U : Set (Space n)} (hU : IsOpen U) {T : ℝ}
    {f : Point n → V} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Ioc 0 T)) (β : List (Option (RIdx n))) :
    ContDiffOn ℝ ∞ (F05GoodWord T β f) (U ×ˢ Ioc 0 T) := by
  induction β with
  | nil => exact hf
  | cons d β ih => exact F05_smooth_background_good_partial hU ih d

end Yau.Proofs.F05Aux
