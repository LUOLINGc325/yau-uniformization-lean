import Yau.Proofs.Y03QuadraticPerturbation
import Yau.Proofs.Y03RowNorm

/-! Uniform perturbation of the row Rayleigh quotient, with an explicit absolute constant. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem perturbation_scalar_bound {δ B r a c q : ℝ}
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2) (hB : 0 ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hlower : (1 - δ) * c ≤ a)
    (hq : q ≤ (r + B * (2 * δ + δ ^ 2)) * c ^ 2) :
    q ≤ (r + 32 * δ * B) * a ^ 2 := by
  have hca : c ≤ 2 * a := by nlinarith
  have hcaSq : c ^ 2 ≤ 4 * a ^ 2 := by nlinarith [sq_nonneg (2 * a - c)]
  have hlow0 : 0 ≤ (1 - δ) * c := mul_nonneg (by linarith) hc
  have hsq : ((1 - δ) * c) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hlow0 hlower 2
  have hdiff : c ^ 2 ≤ a ^ 2 + 2 * δ * c ^ 2 := by nlinarith [mul_nonneg (sq_nonneg δ) (sq_nonneg c)]
  have hδpay := mul_le_mul_of_nonneg_left hcaSq (by positivity : 0 ≤ 2 * δ)
  have hclose : c ^ 2 ≤ a ^ 2 + 8 * δ * a ^ 2 := by nlinarith
  have hcoef : 2 * δ + δ ^ 2 ≤ 3 * δ := by nlinarith
  have hfirst := mul_le_mul_of_nonneg_left hclose hr
  have hsecond : B * (2 * δ + δ ^ 2) * c ^ 2 ≤ B * (3 * δ) * (4 * a ^ 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hcoef hB) hcaSq (sq_nonneg _) (by positivity)
  have hpayR := mul_le_mul_of_nonneg_left hrB (by positivity : 0 ≤ 8 * δ * a ^ 2)
  have hslack : 0 ≤ 12 * δ * B * a ^ 2 := by positivity
  nlinarith

end Yau.Blueprint.Alignment.Y03Proof
