import Yau.Proofs.V03CauchyBinet

/-! Squared Cauchy--Schwarz in the finite scalar coordinates used by the
Plücker minors, with no positive-dimensional premise. -/

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem complex_sum_star_mul_norm_sq_le {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ i, star (a i) * b i‖ ^ 2 ≤ (∑ i, ‖a i‖ ^ 2) * ∑ i, ‖b i‖ ^ 2 := by
  let A : EuclideanSpace ℂ ι := WithLp.toLp 2 a
  let B : EuclideanSpace ℂ ι := WithLp.toLp 2 b
  have h := norm_inner_le_norm (𝕜 := ℂ) A B
  have hs := pow_le_pow_left₀ (norm_nonneg (inner ℂ A B)) h 2
  simpa only [PiLp.inner_apply, RCLike.inner_apply, mul_pow, EuclideanSpace.norm_sq_eq,
    A, B, WithLp.ofLp_toLp, starRingEnd_apply, mul_comm] using hs

end Yau.Blueprint.V03Proof
