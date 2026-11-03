import Yau.Proofs.V01IncreasingBounds

/-! V01 scratch source: the scalar wall threshold follows from the actual
quadratic lower bound on Q and linear growth upper bound on u. -/

noncomputable section

namespace Yau.Blueprint.V01Proof

theorem tail_wall_scalar_bound
    (r u A Q ρ ρtail Cu c C k : ℝ)
    (hCu : 0 < Cu) (hc : 0 < c) (hk : 0 < k)
    (hu : u ≤ Cu * (1 + r))
    (hA : 3 * Cu * (2 + k * (max C 0 + k) / c) ≤ A)
    (huA : A / 3 < u)
    (hQ : c * (1 + r ^ 2) ≤ Q) (htail : ρ - C ≤ ρtail) :
    ρ + k ≤ k⁻¹ * Q + ρtail := by
  let D : ℝ := max C 0 + k
  let M : ℝ := k * D / c
  have hD : 0 < D := by
    dsimp [D]
    linarith [le_max_right C 0]
  have hM : 0 < M := div_pos (mul_pos hk hD) hc
  have hA' : Cu * (2 + M) ≤ A / 3 := by
    dsimp [M, D]
    linarith
  have hur : Cu * (2 + M) < Cu * (1 + r) := hA'.trans_lt (huA.trans_le hu)
  have hr : 1 + M < r := by
    have h := (mul_lt_mul_iff_right₀ hCu).mp hur
    linarith
  have hMr : M ≤ 1 + r ^ 2 := by
    nlinarith [sq_nonneg (r - 1)]
  have hMQ : k * D ≤ Q := by
    calc
      k * D = c * M := by dsimp [M]; field_simp [hc.ne']
      _ ≤ c * (1 + r ^ 2) := mul_le_mul_of_nonneg_left hMr hc.le
      _ ≤ Q := hQ
  have hDQ : D ≤ k⁻¹ * Q := by
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hk).mpr (by nlinarith [hMQ])
  have hDC : C + k ≤ D := by
    dsimp [D]
    linarith [le_max_left C 0]
  linarith

end Yau.Blueprint.V01Proof
