import Yau.Proofs.F01ClosedEquationRestriction

/-! A backward Schauder estimate restricts to a closed buffered patch
inside the actual available clock interval. The containing interval may
end at zero; no regularity at a future time is requested. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem backward_schauder_closed_restrict
    {S : Set (Space n)} {R r a b l s β C : ℝ} {u : Point n → ℝ}
    (hBig : C2 (cylinder S a b) u) (hSch : SchauderBound β (backward R) u C)
    (hSmall : ball (0 : Space n) r ⊆ ball 0 R) (hSpace : ball (0 : Space n) R ⊆ S)
    (hOldClock : Ioc (-(R ^ 2)) 0 ⊆ Icc a b)
    (hInnerClock : Icc l s ⊆ Ioc (-(R ^ 2)) 0) (hls : l < s) :
    SchauderBound β (cylinder (ball 0 r) l s) u C := by
  have hSub : cylinder (ball (0 : Space n) r) l s ⊆ backward R :=
    fun p hp => ⟨hSmall hp.1, hInnerClock hp.2⟩
  obtain ⟨hC2, hTime⟩ := closed_cylinder_c2_and_timeD_restrict hls
    (hSmall.trans hSpace) (hInnerClock.trans hOldClock) hBig
  have hOldTime (p : Point n) (hp : p ∈ backward R) :
      timeD (backward R) u p = timeD (cylinder S a b) u p := by
    have hpBig : p ∈ cylinder S a b := ⟨hSpace hp.1, hOldClock hp.2⟩
    have hSet : {t : ℝ | (p.1, t) ∈ cylinder S a b} = Icc a b := by
      ext t
      exact and_iff_right hpBig.1
    have hd : HasDerivWithinAt (fun t => u (p.1, t))
        (timeD (cylinder S a b) u p) (Icc a b) p.2 := by
      simpa only [timeD, hSet] using (hBig.2.2.2.2.2 p hpBig).hasDerivWithinAt
    have hh := (hd.mono hOldClock).derivWithin (uniqueDiffOn_Ioc (-(R ^ 2)) 0 p.2 hp.2)
    have hOldSet : {t : ℝ | (p.1, t) ∈ backward R} = Ioc (-(R ^ 2)) 0 := by
      ext t
      exact and_iff_right hp.1
    unfold timeD
    rw [hOldSet]
    exact hh
  refine ⟨hC2, hSch.2.1, fun p hp => hSch.2.2.1 p (hSub hp),
    holderBound_restrict hSch.2.2.2.1 hSub, ?_⟩
  apply holderBound_congr_on_native (holderBound_restrict hSch.2.2.2.2 hSub)
  intro p hp
  exact (hOldTime p (hSub hp)).trans (hTime p hp).symm

end Yau.NodeProofs.F01Aux
