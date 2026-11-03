import Yau.Proofs.F03CubicProfile

/-! A genuine compact C² moving bump, before any heat solution is chosen. -/

noncomputable section
open Filter Set
open scoped Topology

namespace Yau.Proofs.F03Aux
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E]

def movingBallBump (R : ℝ) (c : ℝ → E) (p : E × ℝ) : ℝ :=
  positivePower 3 (R ^ 2 - ‖p.1 - c p.2‖ ^ 2)

theorem movingBallBump_contDiff [InnerProductSpace ℝ E]
    (R : ℝ) {c : ℝ → E} (hc : ContDiff ℝ 2 c) :
    ContDiff ℝ 2 (movingBallBump R c) :=
  positivePower_three_contDiff.comp
    (contDiff_const.sub ((contDiff_norm_sq ℝ).comp (contDiff_fst.sub (hc.comp contDiff_snd))))

theorem movingBallBump_nonneg (R : ℝ) (c : ℝ → E) (p : E × ℝ) :
    0 ≤ movingBallBump R c p :=
  pow_nonneg (le_max_left _ _) _

theorem movingBallBump_pos {R : ℝ} (hR : 0 < R) (c : ℝ → E) (x : E) (t : ℝ)
    (hx : ‖x - c t‖ < R) : 0 < movingBallBump R c (x, t) := by
  have hs : 0 < R ^ 2 - ‖x - c t‖ ^ 2 := by nlinarith [norm_nonneg (x - c t)]
  exact pow_pos ((lt_max_iff).mpr (Or.inr hs)) _

theorem movingBallBump_eq_zero {R : ℝ} (hR : 0 ≤ R) (c : ℝ → E) (x : E) (t : ℝ)
    (hx : R ≤ ‖x - c t‖) : movingBallBump R c (x, t) = 0 := by
  have hs : R ^ 2 - ‖x - c t‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg (x - c t)]
  simp only [movingBallBump, positivePower, max_eq_left hs, zero_pow (by omega : 3 ≠ 0)]

theorem movingBallBump_tsupport_subset {R : ℝ} (hR : 0 ≤ R) (c : ℝ → E) (t : ℝ) :
    tsupport (fun x => movingBallBump R c (x, t)) ⊆ Metric.closedBall (c t) R := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  by_contra hn
  exact hx (movingBallBump_eq_zero hR c x t (le_of_not_ge hn))

theorem movingBallBump_hasCompactSupport [ProperSpace E] {R : ℝ} (hR : 0 ≤ R)
    (c : ℝ → E) (t : ℝ) : HasCompactSupport (fun x => movingBallBump R c (x, t)) :=
  (isCompact_closedBall (c t) R).of_isClosed_subset (isClosed_tsupport _)
    (movingBallBump_tsupport_subset hR c t)

/-- The cubic operator estimate has an explicit finite exponential rate.
This is the elementary inequality used after the actual chart derivatives
and uniform ellipticity give its two coefficients. -/
theorem cubicBump_rate_bound (A b s : ℝ) (hb : 0 < b) (hs : 0 ≤ s) :
    A * s ^ 2 - b * s ≤ (A ^ 2 / (4 * b)) * s ^ 3 := by
  have hsq : 0 ≤ (A * s - 2 * b) ^ 2 := sq_nonneg _
  have hpoly : 0 ≤ (A ^ 2 / (4 * b)) * s ^ 2 - A * s + b := by
    have hd : 0 < 4 * b := by positivity
    calc
      0 ≤ (A * s - 2 * b) ^ 2 / (4 * b) := div_nonneg hsq hd.le
      _ = (A ^ 2 / (4 * b)) * s ^ 2 - A * s + b := by
        field_simp
        ring
  have hm := mul_nonneg hs hpoly
  nlinarith only [hm]

end Yau.Proofs.F03Aux
