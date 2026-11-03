import Yau.Proofs.V03BoundarySum
import Yau.Proofs.V03BoundaryDifference

/-! Explicit uniform bounds for finite sums and products of the actual
scalar Fourier traces. No infinite seminorm is converted to a real number. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

theorem finiteTrace_sum_norm_le {ι : Type*} [Fintype ι]
    (u : ι → ℝ → ℂ) {M : ℝ} (hM : ∀ i θ, ‖u i θ‖ ≤ M) (θ : ℝ) :
    ‖∑ i, u i θ‖ ≤ (Fintype.card ι : ℝ) * M := by
  calc
    _ ≤ ∑ i, ‖u i θ‖ := norm_sum_le _ _
    _ ≤ ∑ _ : ι, M := Finset.sum_le_sum (fun i _ => hM i θ)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem finiteTrace_sum_boundaryDSq_le {ι : Type*} [Fintype ι]
    {u : ι → ℝ → ℂ} (hu : ∀ i, Continuous (u i))
    (hp : ∀ i, Function.Periodic (u i) (2 * Real.pi))
    {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ i, boundaryDSq (fun θ (_ : Unit) => u i θ) ≤ ENNReal.ofReal D) :
    boundaryDSq (fun θ (_ : Unit) => ∑ i, u i θ) ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) ^ 2 * D) := by
  have hsum : ∑ i, boundaryDSq (fun θ (_ : Unit) => u i θ) ≤ ∑ _ : ι, ENNReal.ofReal D :=
    Finset.sum_le_sum (fun i _ => hbound i)
  have h := (V03Proof.boundaryDSq_sum_le hu hp).trans
    (mul_le_mul_right hsum (Fintype.card ι : ENNReal))
  rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast, pow_two, mul_assoc]
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

theorem finiteTrace_product_boundaryDSq_le
    {u v : ℝ → ℂ} (hu : Continuous u) (hv : Continuous v)
    (hp : Function.Periodic u (2 * Real.pi))
    (hvp : Function.Periodic v (2 * Real.pi))
    {M N D E : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (huM : ∀ θ, ‖u θ‖ ≤ M) (hvN : ∀ θ, ‖v θ‖ ≤ N)
    (huD : boundaryDSq (fun θ (_ : Unit) => u θ) ≤ ENNReal.ofReal D)
    (hvE : boundaryDSq (fun θ (_ : Unit) => v θ) ≤ ENNReal.ofReal E) :
    boundaryDSq (fun θ (_ : Unit) => u θ * v θ) ≤
      ENNReal.ofReal (2 * N ^ 2 * D + 2 * M ^ 2 * E) := by
  have h := (V03Proof.boundaryDSq_mul_le hu hv hp hvp hM hN huM hvN).trans
    (add_le_add (mul_le_mul_right huD (ENNReal.ofReal (2 * N ^ 2)))
      (mul_le_mul_right hvE (ENNReal.ofReal (2 * M ^ 2))))
  simpa only [ENNReal.ofReal_add (by positivity : 0 ≤ 2 * N ^ 2 * D)
      (by positivity : 0 ≤ 2 * M ^ 2 * E),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * N ^ 2),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * M ^ 2)] using h

end Yau.Blueprint.V02Proof
