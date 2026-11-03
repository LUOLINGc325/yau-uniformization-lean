import Yau.LeafProofs.L05PerturbationPowers

open Filter Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L05Aux

theorem perturb_oscillation_sequence_strong {theta B : ℝ} (htheta : 1/2 ≤ theta)
    (hB : 0 ≤ B) (D : ℕ → ℝ)
    (hStep : ∀ j, D (j+1) ≤ theta*D j+B*(1/16 : ℝ)^j) (j : ℕ) :
    D j ≤ theta^j*(D 0+3*B)-3*B*(1/16 : ℝ)^j := by
  have ht0 : 0 ≤ theta := by linarith
  induction j with
  | zero => simp
  | succ j ih =>
    have hFirst := hStep j
    have hMul := mul_le_mul_of_nonneg_left ih ht0
    have hPow : 0 ≤ B*(1/16 : ℝ)^j := mul_nonneg hB (by positivity)
    have hCoef : 0 ≤ (3*theta-19/16)*(B*(1/16 : ℝ)^j) :=
      mul_nonneg (by linarith) hPow
    rw [pow_succ,pow_succ]
    nlinarith only [hFirst,hMul,hCoef]

theorem perturb_oscillation_sequence {theta B : ℝ} (htheta : 1/2 ≤ theta)
    (hB : 0 ≤ B) (D : ℕ → ℝ)
    (hStep : ∀ j, D (j+1) ≤ theta*D j+B*(1/16 : ℝ)^j) (j : ℕ) :
    D j ≤ theta^j*(D 0+3*B) := by
  have h := perturb_oscillation_sequence_strong htheta hB D hStep j
  have hNonneg : 0 ≤ 3*B*(1/16 : ℝ)^j := by positivity
  linarith

end Yau.LeafProofs.L05Aux
