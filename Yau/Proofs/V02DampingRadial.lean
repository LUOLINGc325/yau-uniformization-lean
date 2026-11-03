import Yau.Proofs.V02DampingHilbert

/-! The actual radial damping has a fixed global Lipschitz constant.
The proof uses only norm inequalities, so realification and empty vectors
require no additional hypotheses. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V02Proof

theorem reciprocalDamping_eq_div {P s : ℝ} (hP : 0 < P) (hs : 0 ≤ s) :
    reciprocalDamping P s = P / (P + s) := by
  unfold reciprocalDamping
  field_simp

theorem radialDamping_difference_bound {P x y : ℝ}
    (hP : 0 < P) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |reciprocalDamping P (x ^ 2) - reciprocalDamping P (y ^ 2)| * y ≤
      2 * |x - y| := by
  have hDx : 0 < P + x ^ 2 := by positivity
  have hDy : 0 < P + y ^ 2 := by positivity
  have hD : 0 < (P + x ^ 2) * (P + y ^ 2) := mul_pos hDx hDy
  have heq : reciprocalDamping P (x ^ 2) - reciprocalDamping P (y ^ 2) =
      -(P * (x - y) * (x + y)) / ((P + x ^ 2) * (P + y ^ 2)) := by
    rw [reciprocalDamping_eq_div hP (sq_nonneg x),
      reciprocalDamping_eq_div hP (sq_nonneg y)]
    field_simp
    <;> ring
  have hcoef : P * y * (x + y) / ((P + x ^ 2) * (P + y ^ 2)) ≤ 2 := by
    apply (div_le_iff₀ hD).mpr
    nlinarith [sq_nonneg (P - x * y), mul_nonneg hP.le (sq_nonneg x),
      mul_nonneg hP.le (sq_nonneg y), mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  rw [heq, abs_div, abs_neg, abs_mul, abs_mul, abs_of_pos hP,
    abs_of_nonneg (add_nonneg hx hy), abs_of_pos hD]
  calc
    _ = (P * y * (x + y) / ((P + x ^ 2) * (P + y ^ 2))) * |x - y| := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)

def radialDamping {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ) (v : E) : E := reciprocalDamping P (‖v‖ ^ 2) • v

theorem radialDamping_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ} (hP : 0 < P) : LipschitzWith 3 (radialDamping (E := E) P) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  let a := reciprocalDamping P (‖v‖ ^ 2)
  let b := reciprocalDamping P (‖w‖ ^ 2)
  have ha : 0 ≤ a := (reciprocalDamping_pos hP (sq_nonneg ‖v‖)).le
  have ha1 : a ≤ 1 := reciprocalDamping_le_one hP (sq_nonneg ‖v‖)
  have hdiff : |a - b| * ‖w‖ ≤ 2 * ‖v - w‖ :=
    (radialDamping_difference_bound hP (norm_nonneg v) (norm_nonneg w)).trans
      (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le v w) (by norm_num))
  have heq : radialDamping P v - radialDamping P w = a • (v - w) + (a - b) • w := by
    unfold radialDamping
    dsimp only [a, b]
    simp only [smul_sub, sub_smul]
    abel
  rw [dist_eq_norm, dist_eq_norm, heq]
  calc
    _ ≤ ‖a • (v - w)‖ + ‖(a - b) • w‖ := norm_add_le _ _
    _ = a * ‖v - w‖ + |a - b| * ‖w‖ := by simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ 1 * ‖v - w‖ + 2 * ‖v - w‖ :=
      add_le_add (mul_le_mul_of_nonneg_right ha1 (norm_nonneg _)) hdiff
    _ = _ := by norm_num <;> ring

end Yau.Blueprint.V02Proof
