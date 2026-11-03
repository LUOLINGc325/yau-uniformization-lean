import Yau.Proofs.F05SmoothSpatialJets
import Yau.Proofs.F05SmoothTimeJets

/-! Actual smooth closed-cylinder data have the literal native chart-C2
predicate, including the one-sided initial and final time derivatives. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 2200000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic

theorem F05_smooth_cylinder_c2 {n : ℕ} {U D : Set (Space n)} (hU : IsOpen U)
    (hDU : D ⊆ U) {S T : ℝ} (hT : 0 < T) (hTS : T ≤ S) {f : Point n → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Icc 0 S)) : C2 (cylinder D 0 T) f := by
  have hS : 0 < S := hT.trans_le hTS
  have hTime : Icc (0 : ℝ) T ⊆ Icc 0 S := fun t ht => ⟨ht.1,ht.2.trans hTS⟩
  have hSub : cylinder D 0 T ⊆ U ×ˢ Icc 0 S := fun p hp => ⟨hDU hp.1,hTime hp.2⟩
  have hSpatial := F05_joint_spatial_jets_smooth hU hf
  have hTimeSmooth := F05_joint_time_derivative_smooth (uniqueDiffOn_Icc hS) hf
  have hTimeSlice (x : Space n) (hx : x ∈ U) :
      ContDiffOn ℝ ∞ (fun t => f (x,t)) (Icc 0 S) :=
    hf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun t ht => ⟨hx,ht⟩)
  have hFiber (p : Point n) (hp : p ∈ cylinder D 0 T) :
      {r | (p.1,r) ∈ cylinder D 0 T} = Icc 0 T := by
    ext r
    exact and_iff_right hp.1
  have hTimeEq (p : Point n) (hp : p ∈ cylinder D 0 T) :
      timeD (cylinder D 0 T) f p = derivWithin (fun t => f (p.1,t)) (Icc 0 S) p.2 := by
    unfold timeD
    rw [hFiber p hp]
    exact (((hTimeSlice p.1 (hDU hp.1)).differentiableOn (by simp) p.2 (hTime hp.2)).hasDerivWithinAt.mono hTime).derivWithin
      (uniqueDiffOn_Icc hT p.2 hp.2)
  refine ⟨hf.continuousOn.mono hSub,hSpatial.1.continuousOn.mono hSub,
    hSpatial.2.continuousOn.mono hSub,(hTimeSmooth.continuousOn.mono hSub).congr hTimeEq,?_,?_⟩
  · intro p hp
    have hSlice : ContDiffOn ℝ ∞ (fun x => f (x,p.2)) U :=
      hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => ⟨hx,hTime hp.2⟩)
    exact (hSlice.contDiffAt (hU.mem_nhds (hDU hp.1))).of_le (by simp)
  · intro p hp
    rw [hFiber p hp]
    exact ((hTimeSlice p.1 (hDU hp.1)).differentiableOn (by simp) p.2 (hTime hp.2)).mono hTime

end Yau.Proofs.F05Aux
