import Yau.Proofs.V03BoundaryDifference

/-! Native finite-component half-order product bounds, retaining the
original ENNReal seminorm and all infinite endpoints. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem boundaryDSq_eq_sum_singleton {ι : Type*} [Fintype ι] (u : ℝ → ι → ℂ) :
    boundaryDSq u = ∑ i, boundaryDSq (fun θ (_ : Unit) => u θ i) := by
  simp only [boundaryDSq, Finset.univ_unique, Finset.sum_singleton]

theorem boundaryDSq_vector_smul_le {ι : Type*} [Fintype ι]
    {c : ℝ → ℂ} {u : ℝ → ι → ℂ} (hc : Continuous c)
    (hu : ∀ i, Continuous (fun θ => u θ i))
    (hcp : Function.Periodic c (2 * Real.pi))
    (hup : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi))
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hcM : ∀ θ, ‖c θ‖ ≤ M) (huN : ∀ θ i, ‖u θ i‖ ≤ N) :
    boundaryDSq (fun θ i => c θ * u θ i) ≤
      (Fintype.card ι : ENNReal) * ENNReal.ofReal (2 * N ^ 2) *
        boundaryDSq (fun θ (_ : Unit) => c θ) +
      ENNReal.ofReal (2 * M ^ 2) * boundaryDSq u := by
  rw [boundaryDSq_eq_sum_singleton (fun θ i => c θ * u θ i), boundaryDSq_eq_sum_singleton u]
  calc
    _ ≤ ∑ i, (ENNReal.ofReal (2 * N ^ 2) * boundaryDSq (fun θ (_ : Unit) => c θ) +
        ENNReal.ofReal (2 * M ^ 2) * boundaryDSq (fun θ (_ : Unit) => u θ i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact boundaryDSq_mul_le hc (hu i) hcp (hup i) hM hN hcM (fun θ => huN θ i)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← Finset.mul_sum]
      ring

end Yau.Blueprint.V03Proof
