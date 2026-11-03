import Yau.Proofs.F04FiniteMass

open Filter Set
open scoped Topology

noncomputable section

namespace Yau.F04Proof

def scalarPositiveEnergy (s : ℝ) : ℝ := (1 / 2 : ℝ) * (max s 0) ^ 2

theorem scalarPositiveEnergy_remainder (s h : ℝ) :
    0 ≤ scalarPositiveEnergy (s + h) - scalarPositiveEnergy s - max s 0 * h ∧
      scalarPositiveEnergy (s + h) - scalarPositiveEnergy s - max s 0 * h ≤ (1 / 2 : ℝ) * h ^ 2 := by
  unfold scalarPositiveEnergy
  rcases le_total 0 s with hs | hs
  · rcases le_total 0 (s + h) with ht | ht
    · constructor <;> rw [max_eq_left hs, max_eq_left ht] <;> nlinarith [sq_nonneg h]
    · have hm : s * (s + h) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs ht
      constructor <;> rw [max_eq_left hs, max_eq_right ht] <;>
        nlinarith [hm, sq_nonneg s, sq_nonneg (s + h)]
  · rcases le_total 0 (s + h) with ht | ht
    · have hm : s * (2 * h + s) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hs (by linarith)
      constructor <;> rw [max_eq_right hs, max_eq_left ht] <;>
        nlinarith [hm, sq_nonneg (s + h)]
    · constructor
      · norm_num [max_eq_right hs, max_eq_right ht]
      · rw [max_eq_right hs, max_eq_right ht]
        nlinarith [sq_nonneg h]

theorem hasFDerivAt_of_quadratic_remainder {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (x : E) (L : E →L[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hrem : ∀ h, |F (x + h) - F x - L h| ≤ C * ‖h‖ ^ 2) : HasFDerivAt F L x := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  have hCp : 0 < C + 1 := by linarith
  filter_upwards [Metric.ball_mem_nhds (0 : E) (div_pos hε hCp)] with h hh
  have hhn : ‖h‖ < ε / (C + 1) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  have hcap : C * ‖h‖ ≤ ε := by
    have hp := (lt_div_iff₀ hCp).mp hhn
    nlinarith [norm_nonneg h]
  change |F (x + h) - F x - L h| ≤ ε * ‖h‖
  calc
    _ ≤ C * ‖h‖ ^ 2 := hrem h
    _ = (C * ‖h‖) * ‖h‖ := by ring
    _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hcap (norm_nonneg h)

end Yau.F04Proof
