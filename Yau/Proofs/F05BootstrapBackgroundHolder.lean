import Yau.Proofs.F05CompactHolder
import Yau.Proofs.F05BootstrapQuotientSource
import Yau.Proofs.F05BootstrapLocalBounds

/-! A fixed smooth positive-time background has local Holder bounds up
to the terminal face. A genuine earlier positive time is translated to
zero before applying the existing compact cylinder estimate. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_positive_smooth_local_holder {ν : Option (RIdx n)} {T α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {f : Point n → V}
    (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 3 ×ˢ Ioc 0 T)) : F05LocalHolder α ν T f := by
  intro r hr hr2 s hs hsT
  let s0 := s/2
  let L := T-s0
  let g : Point n → V := fun z => f (z.1,z.2+s0)
  have hs0 : 0 < s0 := by dsimp only [s0]; positivity
  have hL : 0 < L := by dsimp only [L,s0]; linarith
  have hSmooth : ContDiffOn ℝ ∞ g (Metric.ball 0 3 ×ˢ Icc 0 L) := by
    apply hf.comp (contDiffOn_fst.prodMk (contDiffOn_snd.add contDiffOn_const))
    intro p hp
    exact ⟨hp.1,by linarith [hp.2.1],by dsimp only [L] at hp; linarith [hp.2.2]⟩
  obtain ⟨C,hC,hBudget⟩ := F05_compact_cylinder_holder Metric.isOpen_ball
    (isCompact_closedBall (0 : Space n) r) (convex_closedBall (0 : Space n) r)
    (Metric.closedBall_subset_ball (hr2.trans (by norm_num : (2 : ℝ) < 3))) hL hSmooth
  have hMap : MapsTo (F05GoodShift none s0) (region ν r ×ˢ Icc s T)
      (Metric.closedBall 0 r ×ˢ Icc 0 L) := by
    intro p hp
    refine ⟨?_,?_,?_⟩
    · simpa only [F05GoodShift,timeTranslatePoint,Metric.mem_closedBall,dist_zero_right] using hp.1.1
    · change 0 ≤ p.2+(-s0)
      dsimp only [s0]
      linarith [hp.2.1]
    · change p.2+(-s0) ≤ L
      dsimp only [L]
      linarith [hp.2.2]
  have hShift := F05_good_shift_holder (hBudget α hα hα1 L le_rfl) hMap
  refine ⟨C,hC,holderBound_congr_on hShift ?_⟩
  intro p hp
  change f (p.1,p.2+(-s0)+s0) = f p
  simp only [neg_add_cancel_right,Prod.eta]

end Yau.Proofs.F05Aux
