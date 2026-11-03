import Yau.Proofs.V03BoundarySum
import Yau.Proofs.V03BoundaryDifference

/-! Native finite covector contractions obey the original half-order
product estimate, with all infinite endpoints and empty ranks retained. -/

open scoped Topology Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem boundaryDSq_dotProduct_le {ι : Type*} [Fintype ι]
    {u v : ℝ → ι → ℂ}
    (hu : ∀ i, Continuous (fun θ => u θ i)) (hv : ∀ i, Continuous (fun θ => v θ i))
    (hup : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi))
    (hvp : ∀ i, Function.Periodic (fun θ => v θ i) (2 * Real.pi))
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hum : ∀ θ i, ‖u θ i‖ ≤ M) (hvn : ∀ θ i, ‖v θ i‖ ≤ N) :
    boundaryDSq (fun θ (_ : Unit) => u θ ⬝ᵥ v θ) ≤
      (Fintype.card ι : ENNReal) *
        (ENNReal.ofReal (2 * N ^ 2) * boundaryDSq u +
          ENNReal.ofReal (2 * M ^ 2) * boundaryDSq v) := by
  have hp (i : ι) := boundaryDSq_mul_le (hu i) (hv i) (hup i) (hvp i) hM hN
    (fun θ => hum θ i) (fun θ => hvn θ i)
  change boundaryDSq (fun θ (_ : Unit) => ∑ i, u θ i * v θ i) ≤ _
  calc
    _ ≤ (Fintype.card ι : ENNReal) *
        ∑ i, boundaryDSq (fun θ (_ : Unit) => u θ i * v θ i) :=
      boundaryDSq_sum_le (fun i => (hu i).mul (hv i)) (fun i => (hup i).mul (hvp i))
    _ ≤ (Fintype.card ι : ENNReal) * ∑ i,
        (ENNReal.ofReal (2 * N ^ 2) * boundaryDSq (fun θ (_ : Unit) => u θ i) +
          ENNReal.ofReal (2 * M ^ 2) * boundaryDSq (fun θ (_ : Unit) => v θ i)) := by
      gcongr with i
      exact hp i
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← boundaryDSq_eq_sum_singleton u, ← boundaryDSq_eq_sum_singleton v]

theorem dotProduct_norm_le_card_mul {ι : Type*} [Fintype ι] {u v : ι → ℂ}
    {M N : ℝ} (hu : ∀ i, ‖u i‖ ≤ M) (hv : ∀ i, ‖v i‖ ≤ N)
    (hM : 0 ≤ M) : ‖u ⬝ᵥ v‖ ≤ (Fintype.card ι : ℝ) * M * N := by
  calc
    _ ≤ ∑ i, ‖u i * v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, M * N := Finset.sum_le_sum (fun i _ => by
      rw [norm_mul]
      exact mul_le_mul (hu i) (hv i) (norm_nonneg _) hM)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Yau.Blueprint.V03Proof
