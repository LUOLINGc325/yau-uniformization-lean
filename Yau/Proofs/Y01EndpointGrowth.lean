import Yau.Proofs.Y01PolynomialGrowth
import Yau.Proofs.Y01SqrtEnvelopes

/-! Polynomial costs at two adjacent canonical clock values are absorbed
in one center exponent; the only leading exponential remains exp(delta/2). -/

noncomputable section

namespace Yau.Proofs.Y01Aux

theorem endpoint_real_power_product (hm p : ℝ) (hp : 0 ≤ p) :
    ∃ q : ℝ, p ≤ q ∧ ∀ s t : ℝ, 2 ≤ s → 0 ≤ t → t ≤ Real.exp hm * s →
      (1 + s) ^ p * (1 + t) ^ p ≤ s ^ q := by
  let K := (2 * (1 + Real.exp hm)) ^ p
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  have hdiv : 0 ≤ K / Real.log 2 := by positivity
  refine ⟨K / Real.log 2 + 2 * p, by linarith, ?_⟩
  intro s t hs ht0 ht
  have hs0 : 0 < s := by linarith
  have hleft : (1 + s) ^ p ≤ (2 * s) ^ p :=
    Real.rpow_le_rpow (by linarith) (by linarith) hp
  have hright : (1 + t) ^ p ≤ ((1 + Real.exp hm) * s) ^ p :=
    Real.rpow_le_rpow (by linarith) (by nlinarith) hp
  have hKpow : K ≤ s ^ (K / Real.log 2) := by
    have h := constant_le_real_power hK (show 1 ≤ s - 1 by linarith)
    simpa only [show 1 + (s - 1) = s by ring] using h
  calc
    _ ≤ (2 * s) ^ p * ((1 + Real.exp hm) * s) ^ p :=
      mul_le_mul hleft hright (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by positivity) _)
    _ = K * s ^ (2 * p) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hs0.le,
        Real.mul_rpow (by positivity : (0 : ℝ) ≤ 1 + Real.exp hm) hs0.le]
      dsimp [K]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ 1 + Real.exp hm)]
      rw [show 2 * p = p + p by ring, Real.rpow_add hs0]
      ring
    _ ≤ s ^ (K / Real.log 2) * s ^ (2 * p) :=
      mul_le_mul_of_nonneg_right hKpow (Real.rpow_nonneg hs0.le _)
    _ = _ := (Real.rpow_add hs0 _ _).symm

theorem inverse_growth_sqrt_envelope {s Δ p x : ℝ} (hs : 1 ≤ s) (hp : 0 ≤ p)
    (hx : x ≤ s ^ p * Real.exp (Δ / 2)) :
    x ≤ Real.exp (Δ / 2 + (4 * |p|) * Real.sqrt s) := by
  have hpoly : s ^ p ≤ Real.exp ((4 * |p|) * Real.sqrt s) :=
    (Real.rpow_le_rpow (by linarith) (by linarith : s ≤ 1 + s) hp).trans
      (polynomial_le_sqrt_envelope hs)
  calc
    _ ≤ s ^ p * Real.exp (Δ / 2) := hx
    _ ≤ Real.exp ((4 * |p|) * Real.sqrt s) * Real.exp (Δ / 2) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Yau.Proofs.Y01Aux
