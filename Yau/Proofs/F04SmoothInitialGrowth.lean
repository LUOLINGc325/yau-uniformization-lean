import Yau.Proofs.F05SmoothTimeJets
import Yau.LeafProofs.L18

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic

/-- An actual smooth zero-initial local particular solution has a genuine
 uniform compact O(t) bound. Its one-sided time derivative is produced
 from the smooth closed slab and unique derivatives, and bounded on the
 actual compact product before the mean-value estimate is applied. -/
theorem smooth_zeroInitial_compact_growth
    {n : ℕ} {O : Set (Space n)} {S : ℝ} (hS : 0 < S)
    {p : Point n → ℝ} (hp : ContDiffOn ℝ ∞ p (O ×ˢ Icc 0 S))
    (h0 : ∀ x ∈ O, p (x, 0) = 0)
    (K : Set (Space n)) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ t ∈ Icc 0 S, |p (x, t)| ≤ C * t := by
  let D := fun q : Point n => derivWithin (fun t => p (q.1, t)) (Icc 0 S) q.2
  have hD : ContinuousOn D (O ×ˢ Icc 0 S) :=
    (Yau.Proofs.F05Aux.F05_joint_time_derivative_smooth (uniqueDiffOn_Icc hS) hp).continuousOn
  obtain ⟨A, hA⟩ := (hK.prod isCompact_Icc).bddAbove_image
    (hD.norm.mono (prod_mono hKO (Subset.refl _)))
  let C := max A 0
  refine ⟨C, le_max_right _ _, ?_⟩
  intro x hx t ht
  have hSlice : ContDiffOn ℝ ∞ (fun s => p (x, s)) (Icc 0 S) :=
    hp.comp (contDiffOn_const.prodMk contDiffOn_id) (fun s hs => ⟨hKO hx, hs⟩)
  have hd (s : ℝ) (hs : s ∈ Icc 0 S) :
      HasDerivWithinAt (fun r => p (x, r)) (D (x, s)) (Icc 0 S) s :=
    (hSlice s hs).differentiableWithinAt (by simp) |>.hasDerivWithinAt
  have hb (s : ℝ) (hs : s ∈ Icc 0 S) : ‖D (x, s)‖ ≤ C :=
    (hA ⟨(x, s), ⟨hx, hs⟩, rfl⟩).trans (le_max_left _ _)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc 0 S)
    (show (0 : ℝ) ∈ Icc 0 S from ⟨le_rfl, hS.le⟩) ht
  simpa only [h0 x (hKO hx), sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] using hm

end Yau.F04Proof
