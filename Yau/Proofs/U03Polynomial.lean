import Yau.Proofs.U03PolynomialAlgebra
import Mathlib.Analysis.Complex.AbsMax

/-! Sharp vector-valued polynomial growth, with no dimension-dependent factor. -/

open scoped Topology BigOperators

noncomputable section
namespace Yau.Blueprint.U03Proof

variable {n : ℕ}

theorem polynomial_growth_closedBall
    (P : PolyMap n) (m : ℕ) (hPm : P.degree ≤ m)
    {R1 R2 B : ℝ} (hR1 : 0 < R1) (hR12 : R1 < R2)
    (hB : ∀ w : ComplexVector n, ‖w‖ ≤ R1 → ‖P.eval w‖ ≤ B)
    {z : ComplexVector n} (hz : ‖z‖ ≤ R2) :
    ‖P.eval z‖ ≤ (R2 / R1) ^ m * B := by
  have hR2 : 0 < R2 := hR1.trans hR12
  let t : ℝ := R1 / R2
  have ht : 0 < t := div_pos hR1 hR2
  have ht1 : t < 1 := (div_lt_one hR2).2 hR12
  have htn : ‖(t : ℂ)‖ = t := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  let v : ComplexVector n := (t : ℂ) • z
  have hv : ‖v‖ ≤ R1 := by
    change ‖(t : ℂ) • z‖ ≤ R1
    rw [norm_smul, htn]
    calc
      t * ‖z‖ ≤ t * R2 := mul_le_mul_of_nonneg_left hz ht.le
      _ = R1 := div_mul_cancel₀ R1 hR2.ne'
  have hF : Differentiable ℂ (reflectedLine P m v) :=
    reflectedLine_differentiable P m v
  have hFt : ‖reflectedLine P m v (t : ℂ)‖ ≤ B := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      (U := Metric.ball (0 : ℂ) 1) Metric.isBounded_ball hF.diffContOnCl ?_ ?_
    · intro w hw
      have hwn : ‖w‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using
          Metric.frontier_ball_subset_sphere hw
      have hwne : w ≠ 0 := by
        intro hw0
        simpa [hw0] using hwn
      rw [reflectedLine_eq hPm v hwne, norm_smul, norm_pow, hwn, one_pow, one_mul]
      apply hB
      simpa only [norm_smul, norm_inv, hwn, inv_one, one_mul] using hv
    · apply subset_closure
      simpa only [Metric.mem_ball, dist_zero_right, htn] using ht1
  have hcancel : (t : ℂ)⁻¹ • v = z := by
    exact inv_smul_smul₀ htne z
  have hineq : t ^ m * ‖P.eval z‖ ≤ B := by
    simpa only [reflectedLine_eq hPm v htne, hcancel, norm_smul, norm_pow, htn] using hFt
  have hrec : (R2 / R1) * t = 1 := by
    dsimp only [t]
    field_simp [hR1.ne', hR2.ne']
    <;> ring
  calc
    ‖P.eval z‖ = (R2 / R1) ^ m * (t ^ m * ‖P.eval z‖) := by
      rw [← mul_assoc, ← mul_pow, hrec, one_pow, one_mul]
    _ ≤ (R2 / R1) ^ m * B :=
      mul_le_mul_of_nonneg_left hineq (pow_nonneg (div_pos hR2 hR1).le m)

end Yau.Blueprint.U03Proof
