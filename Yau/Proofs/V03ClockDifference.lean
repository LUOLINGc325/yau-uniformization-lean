import Yau.Proofs.V03TimeScalars
import Yau.Proofs.V03BoundaryDifference

/-! The original exponential clock has a global boundary difference bound
from its actual physical-time endpoint bound, with no lower-time bound. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem scaled_exp_sub_le {s T x y : ℝ} (hs : 0 ≤ s)
    (hx : s * Real.exp x ≤ T) (hxy : y ≤ x) :
    s * Real.exp x - s * Real.exp y ≤ T * (x - y) := by
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (y - x))
    (mul_nonneg hs (Real.exp_nonneg x))
  have hprod : s * Real.exp x * Real.exp (y - x) = s * Real.exp y := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hprod] at he
  have hmul := mul_le_mul_of_nonneg_right hx (sub_nonneg.mpr hxy)
  nlinarith

theorem scaled_exp_abs_sub_le {s T x y : ℝ} (hs : 0 ≤ s)
    (hx : s * Real.exp x ≤ T) (hy : s * Real.exp y ≤ T) :
    |s * Real.exp x - s * Real.exp y| ≤ T * |x - y| := by
  rcases le_total y x with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxy) hs)), abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact scaled_exp_sub_le hs hx hxy
  · rw [abs_sub_comm, abs_sub_comm x y]
    rw [abs_of_nonneg (sub_nonneg.mpr
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hyx) hs)), abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact scaled_exp_sub_le hs hy hyx

theorem admissible_clock_difference {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} {j : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) (θ τ : ℝ) :
    |discTime F (circlePoint θ) - discTime F (circlePoint τ)| ≤
      (2 * d.T) * ‖F.w (circlePoint θ) - F.w (circlePoint τ)‖ := by
  have htθ := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  have htτ := admissible_discTime_mem hF (circlePoint_mem_closedBall τ)
  have hT : 0 ≤ d.T := htθ.1.le.trans htθ.2.le
  have hh := scaled_exp_abs_sub_le hF.2.2.2.1.le htθ.2.le htτ.2.le
  have hre := Complex.abs_re_le_norm (F.w (circlePoint θ) - F.w (circlePoint τ))
  change |discTime F (circlePoint θ) - discTime F (circlePoint τ)| ≤ _ at hh
  have heq : |2 * (F.w (circlePoint θ)).re - 2 * (F.w (circlePoint τ)).re| =
      2 * |(F.w (circlePoint θ) - F.w (circlePoint τ)).re| := by
    rw [Complex.sub_re, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [heq] at hh
  exact hh.trans (by nlinarith)

end Yau.Blueprint.V03Proof
