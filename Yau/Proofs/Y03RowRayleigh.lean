import Yau.Proofs.Y03RayleighPerturbation

/-! Quantitative Rayleigh control on the actual perturbed unitary row image. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem perturbed_row_rayleigh_bound (μ ν : Fin n → ℝ) (U E : Herm n)
    (hU : Unitary U) {δ B r : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B) (hE : matOpNorm E ≤ δ)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ B)
    (horder : ∀ v : Fin n → ℂ, (∑ i, μ i * ‖(v ᵥ* U) i‖ ^ 2) ≤ ∑ i, ν i * ‖v i‖ ^ 2)
    (c : ComplexVector n) (hc : ∀ i, c i ≠ 0 → ν i ≤ r) :
    (∑ i, μ i * ‖rowApply ((1 + E) * U) c i‖ ^ 2) ≤
      (r + 32 * δ * B) * ‖rowApply ((1 + E) * U) c‖ ^ 2 := by
  let u := rowApply U c
  let e := rowApply U (rowApply E c)
  let a := rowApply ((1 + E) * U) c
  have hdecomp : a = u + e := by
    dsimp only [a, u, e]
    rw [rowApply_mul]
    rw [← rowApply_add]
    apply congrArg (rowApply U)
    apply WithLp.ofLp_injective
    change WithLp.ofLp c ᵥ* (1 + E) = WithLp.ofLp c + WithLp.ofLp c ᵥ* E
    rw [Matrix.vecMul_add, Matrix.vecMul_one]
  have hunorm : ‖u‖ = ‖c‖ := rowApply_norm_unitary hU c
  have henorm : ‖e‖ ≤ δ * ‖c‖ := by
    rw [show ‖e‖ = ‖rowApply E c‖ from rowApply_norm_unitary hU _]
    exact (rowApply_norm_le E c).trans (mul_le_mul_of_nonneg_right hE (norm_nonneg c))
  have hlower : (1 - δ) * ‖c‖ ≤ ‖a‖ := by
    have htri : ‖u‖ ≤ ‖a‖ + ‖e‖ := by
      calc
        _ = ‖a - e‖ := by rw [hdecomp, add_sub_cancel_right]
        _ ≤ _ := norm_sub_le _ _
    rw [hunorm] at htri
    linarith
  have hqc : (∑ i, μ i * ‖u i‖ ^ 2) ≤ r * ‖c‖ ^ 2 := by
    apply (horder (WithLp.ofLp c)).trans
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : c i = 0
    · rw [hi, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right (hc i hi) (sq_nonneg _)
  have hp := diagonal_quadratic_perturbation μ B hB hμ u e
  rw [← hdecomp, hunorm] at hp
  have hsq : ‖e‖ ^ 2 ≤ δ ^ 2 * ‖c‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg e) henorm 2
  have hcross := mul_le_mul_of_nonneg_left henorm (by positivity : 0 ≤ 2 * ‖c‖)
  have herror : 2 * ‖c‖ * ‖e‖ + ‖e‖ ^ 2 ≤ (2 * δ + δ ^ 2) * ‖c‖ ^ 2 := by nlinarith
  have hpay := mul_le_mul_of_nonneg_left herror hB
  have hq : (∑ i, μ i * ‖a i‖ ^ 2) ≤ (r + B * (2 * δ + δ ^ 2)) * ‖c‖ ^ 2 := by nlinarith
  exact perturbation_scalar_bound hδ hδ' hB hr hrB (norm_nonneg a) (norm_nonneg c) hlower hq

end Yau.Blueprint.Alignment.Y03Proof
