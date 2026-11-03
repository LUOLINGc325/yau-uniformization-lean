import Yau.Proofs.V04WallErrorScalar

open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux

theorem wallScalar_derivative_bounds {p : ℝ → ℝ} (hp : ContDiff ℝ ∞ p)
    {M A u : ℝ} (hM : 1 ≤ M) (hA : 1 ≤ A)
    (hδ : 0 < p (u / A)) (hδone : p (u / A) ≤ 1)
    (hd : |deriv p (u / A)| ≤ M) (hdd : |deriv (deriv p) (u / A)| ≤ M) :
    |deriv (wallScalar p A) u| ≤ M * (p (u / A) ^ 3)⁻¹ ∧
    |deriv (deriv (wallScalar p A)) u| ≤
      (2 * M ^ 2 + M) * (p (u / A) ^ 3)⁻¹ := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hfrac : |deriv p (u / A) / A| ≤ M := by
    rw [abs_div, abs_of_pos hA0]
    apply (div_le_iff₀ hA0).2
    exact hd.trans (le_mul_of_one_le_right hM0 hA)
  have hfrac2 : (deriv p (u / A) / A) ^ 2 ≤ M ^ 2 := by
    nlinarith [sq_abs (deriv p (u / A) / A), abs_nonneg (deriv p (u / A) / A)]
  have hfracdd : |deriv (deriv p) (u / A)| / A ^ 2 ≤ M := by
    apply (div_le_iff₀ (sq_pos_of_pos hA0)).2
    exact hdd.trans (le_mul_of_one_le_right hM0 hA2)
  have hδ2 : 0 < p (u / A) ^ 2 := pow_pos hδ 2
  have hδ3 : 0 < p (u / A) ^ 3 := pow_pos hδ 3
  have hweight : (p (u / A) ^ 2)⁻¹ ≤ (p (u / A) ^ 3)⁻¹ := by
    apply (inv_le_inv₀ hδ2 hδ3).2
    calc
      p (u / A) ^ 3 = p (u / A) ^ 2 * p (u / A) := by ring
      _ ≤ p (u / A) ^ 2 * 1 := mul_le_mul_of_nonneg_left hδone (sq_nonneg _)
      _ = _ := mul_one _
  constructor
  · rw [wallScalar_deriv (hp.differentiable (by simp) _) hδ.ne']
    simp only [abs_div, abs_neg, abs_of_pos hδ2, abs_of_pos hA0]
    calc
      (|deriv p (u / A)| / A) / p (u / A) ^ 2 ≤ M / p (u / A) ^ 2 :=
        div_le_div_of_nonneg_right (by simpa only [abs_div, abs_of_pos hA0] using hfrac) hδ2.le
      _ ≤ M * (p (u / A) ^ 3)⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hweight hM0
  · rw [wallScalar_secondDeriv hp hA0.ne' hδ.ne']
    calc
      |2 * (deriv p (u / A) / A) ^ 2 / p (u / A) ^ 3 -
          (deriv (deriv p) (u / A) / A ^ 2) / p (u / A) ^ 2| ≤
          |2 * (deriv p (u / A) / A) ^ 2 / p (u / A) ^ 3| +
            |(deriv (deriv p) (u / A) / A ^ 2) / p (u / A) ^ 2| := abs_sub _ _
      _ = 2 * (deriv p (u / A) / A) ^ 2 / p (u / A) ^ 3 +
          (|deriv (deriv p) (u / A)| / A ^ 2) / p (u / A) ^ 2 := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (deriv p (u / A) / A) ^ 2 / p (u / A) ^ 3)]
        simp only [abs_div, abs_of_pos hδ2, abs_of_pos (sq_pos_of_pos hA0)]
      _ ≤ 2 * M ^ 2 / p (u / A) ^ 3 + M / p (u / A) ^ 2 := by gcongr
      _ ≤ (2 * M ^ 2 + M) * (p (u / A) ^ 3)⁻¹ := by
        have hmw : M / p (u / A) ^ 2 ≤ M * (p (u / A) ^ 3)⁻¹ := by
          calc
            M / p (u / A) ^ 2 = M * (p (u / A) ^ 2)⁻¹ := div_eq_mul_inv _ _
            _ ≤ _ := mul_le_mul_of_nonneg_left hweight hM0
        calc
          _ ≤ 2 * M ^ 2 / p (u / A) ^ 3 + M * (p (u / A) ^ 3)⁻¹ := add_le_add le_rfl hmw
          _ = _ := by ring

end Yau.Blueprint.V04Proof.WallErrorAux
