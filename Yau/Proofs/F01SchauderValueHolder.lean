import Yau.Proofs.F01ClampedAffineHolder
import Mathlib.Analysis.Calculus.MeanValue

/-! A genuine Schauder bound controls the function itself in the
parabolic Holder norm on the fixed closed backward core. Spatial and
one-sided time mean-value estimates also cover the two time faces. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem schauder_fixed_core_value_holder
    {β C : ℝ} (hβ : β ≤ 1) {u : Point n → ℝ}
    (hu : SchauderBound β (cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0) u C) :
    HolderBound β (cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0) u C := by
  let Q := cylinder (ball (0 : Space n) (1 / 2)) (-(1 / 2)) 0
  have hSpace (s : ℝ) (hs : s ∈ Icc (-(1 / 2) : ℝ) 0)
      (x y : Space n) (hx : x ∈ ball 0 (1 / 2)) (hy : y ∈ ball 0 (1 / 2)) :
      |u (x, s) - u (y, s)| ≤ C * ‖x - y‖ := by
    have hd (z : Space n) (hz : z ∈ ball 0 (1 / 2)) :
        HasFDerivWithinAt (fun w => u (w, s)) (spatialD u (z, s)) (ball 0 (1 / 2)) z :=
      ((hu.1.2.2.2.2.1 (z, s) ⟨hz, hs⟩).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
    simpa only [Real.norm_eq_abs] using
      (convex_ball (0 : Space n) (1 / 2)).norm_image_sub_le_of_norm_hasFDerivWithin_le hd
        (fun z hz => (hu.2.2.1 (z, s) ⟨hz, hs⟩).2) hy hx
  have hTime (x : Space n) (hx : x ∈ ball 0 (1 / 2))
      (s t : ℝ) (hs : s ∈ Icc (-(1 / 2) : ℝ) 0) (ht : t ∈ Icc (-(1 / 2) : ℝ) 0) :
      |u (x, s) - u (x, t)| ≤ C * |s - t| := by
    have hSet : {s : ℝ | (x, s) ∈ Q} = Icc (-(1 / 2) : ℝ) 0 := by
      ext s
      exact and_iff_right hx
    have hd (s : ℝ) (hs : s ∈ Icc (-(1 / 2) : ℝ) 0) :
        HasDerivWithinAt (fun t => u (x, t)) (timeD Q u (x, s)) (Icc (-(1 / 2)) 0) s := by
      have hh := (hu.1.2.2.2.2.2 (x, s) ⟨hx, hs⟩).hasDerivWithinAt
      change HasDerivWithinAt (fun t => u (x, t)) (timeD Q u (x, s)) {t | (x, t) ∈ Q} s at hh
      rwa [hSet] at hh
    simpa only [Real.norm_eq_abs] using
      (convex_Icc (-(1 / 2) : ℝ) 0).norm_image_sub_le_of_norm_hasDerivWithin_le hd
        (fun s hs => (hu.2.2.2.2).2.1 (x, s) ⟨hx, hs⟩) ht hs
  refine ⟨hu.2.1, (fun p hp => by simpa only [Real.norm_eq_abs] using (hu.2.2.1 p hp).1), ?_⟩
  intro p hp q hq
  have hd : ‖p.1 - q.1‖ ≤ 1 := by
    have hpN : ‖p.1‖ < 1 / 2 := by simpa only [mem_ball, dist_zero_right] using hp.1
    have hqN : ‖q.1‖ < 1 / 2 := by simpa only [mem_ball, dist_zero_right] using hq.1
    exact (norm_sub_le _ _).trans (by linarith)
  have ht : |p.2 - q.2| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hp.2.1, hp.2.2, hq.2.1, hq.2.2]
  have hdp : ‖p.1 - q.1‖ ≤ ‖p.1 - q.1‖ ^ β := by
    simpa only [Real.one_rpow, one_mul] using
      linear_le_bounded_holder_power (norm_nonneg _) zero_lt_one hd hβ
  have htp : |p.2 - q.2| ≤ |p.2 - q.2| ^ (β / 2) := by
    simpa only [Real.one_rpow, one_mul] using
      linear_le_bounded_holder_power (abs_nonneg _) zero_lt_one ht (by linarith : β / 2 ≤ 1)
  have hTri : |u p - u q| ≤ |u (p.1, p.2) - u (q.1, p.2)| +
      |u (q.1, p.2) - u (q.1, q.2)| := by
    convert abs_add_le (u (p.1, p.2) - u (q.1, p.2)) (u (q.1, p.2) - u (q.1, q.2)) using 1 <;> ring
  change |u p - u q| ≤ C * holderWeight β p q
  exact hTri.trans ((add_le_add
    ((hSpace p.2 hp.2 p.1 q.1 hp.1 hq.1).trans (mul_le_mul_of_nonneg_left hdp hu.2.1))
    ((hTime q.1 hq.1 p.2 q.2 hp.2 hq.2).trans (mul_le_mul_of_nonneg_left htp hu.2.1))).trans_eq
      (by unfold holderWeight; ring))

end Yau.NodeProofs.F01Aux
