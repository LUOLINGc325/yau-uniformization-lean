import Yau.Proofs.F01ClosedParabolicC2
import Yau.Proofs.F01ZeroExtensionSpaceJets
import Yau.Proofs.F01ZeroExtensionTimeJet

/-! Zero extension is genuinely parabolic C² across the initial surface
when the original value and original first time jet vanish there. Spatial
jets and the time jet are computed and glued; joint C² is not asserted. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem forwardZeroSpaceTime_parabolic_C2 {F : Point n → ℝ}
    {S : Set (Space n)} {a T : ℝ} (hS : IsOpen S) (hT : 0 < T) (ha : a < T)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Icc 0 T))
    (hF0 : ∀ x ∈ S, F (x, 0) = 0)
    (hInit : ∀ x ∈ S, HasDerivWithinAt (fun s => F (x, s)) 0 (Icc 0 T) 0) :
    C2 (S ×ˢ Icc a T) (forwardZeroSpaceTime F) := by
  let D : Point n → ℝ := fun p => derivWithin (fun s => F (p.1, s)) (Icc 0 T) p.2
  have hOld := closed_slab_parabolic_C2 hS (uniqueDiffOn_Icc hT) hF
  have hD : ContinuousOn D (S ×ˢ Icc 0 T) :=
    (closed_slab_time_derivWithin_smooth hS (uniqueDiffOn_Icc hT) hF).continuousOn
  have hD0 (x : Space n) (hx : x ∈ S) : D (x, 0) = 0 :=
    (hInit x hx).derivWithin ((uniqueDiffOn_Icc hT) 0 ⟨le_rfl, hT.le⟩)
  have hOriginalJet (x : Space n) (hx : x ∈ S) (s : ℝ) (hs : s ∈ Icc 0 T) :
      HasDerivWithinAt (fun r => F (x, r)) (D (x, s)) (Icc 0 T) s :=
    ((contDiffOn_time_slice hF hx s hs).differentiableWithinAt (by simp)).hasDerivWithinAt
  have hJet (p : Point n) (hp : p ∈ S ×ˢ Icc a T) :
      HasDerivWithinAt (fun s => forwardZeroSpaceTime F (p.1, s))
        (forwardZeroSpaceTime D p) (Icc a T) p.2 :=
    forwardZeroExtension_time_jet hT (hF0 p.1 hp.1) (hD0 p.1 hp.1)
      (hOriginalJet p.1 hp.1) hp.2
  have hset (p : Point n) (hp : p ∈ S ×ˢ Icc a T) :
      {t : ℝ | (p.1, t) ∈ S ×ˢ Icc a T} = Icc a T := by
    ext t
    exact and_iff_right hp.1
  have htime : ContinuousOn (timeD (S ×ˢ Icc a T) (forwardZeroSpaceTime F)) (S ×ˢ Icc a T) := by
    apply (forwardZeroSpaceTime_continuousOn hT.le hD hD0).congr
    intro p hp
    unfold timeD
    rw [hset p hp]
    exact (hJet p hp).derivWithin ((uniqueDiffOn_Icc ha) p.2 hp.2)
  refine ⟨forwardZeroSpaceTime_continuousOn hT.le hOld.1 hF0, ?_, ?_, htime, ?_, ?_⟩
  · rw [spatialD_forwardZeroSpaceTime]
    exact forwardZeroSpaceTime_continuousOn hT.le hOld.2.1
      (fun x hx => spatialD_initial_zero hS hF0 hx)
  · rw [spatialDD_forwardZeroSpaceTime]
    exact forwardZeroSpaceTime_continuousOn hT.le hOld.2.2.1
      (fun x hx => spatialDD_initial_zero hS hF0 hx)
  · intro p hp
    by_cases ht : p.2 ≤ 0
    · have heq : (fun x => forwardZeroSpaceTime F (x, p.2)) = (fun _ => (0 : ℝ)) := by
        funext x
        exact forwardZeroExtension_eq_of_nonpos (fun t => F (x, t)) ht
      rw [heq]
      exact contDiff_const.contDiffAt
    · have heq : (fun x => forwardZeroSpaceTime F (x, p.2)) = (fun x => F (x, p.2)) := by
        funext x
        exact if_neg ht
      rw [heq]
      exact (closed_slab_slice_jets hF hS hp.1 ⟨(le_of_not_ge ht), hp.2.2⟩).1
  · intro p hp
    rw [hset p hp]
    exact (hJet p hp).differentiableWithinAt

end Yau.NodeProofs.F01Aux
