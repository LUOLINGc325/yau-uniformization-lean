import Yau.Proofs.V03GagliardoVector

/-! Ambient Euclidean differences and one scalar difference control the
original boundary seminorm of a scalar coefficient. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem boundaryDSq_sum_index {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ℝ → ι → ℂ) (v : ℝ → κ → ℂ) :
    boundaryDSq (fun θ => Sum.elim (u θ) (v θ)) = boundaryDSq u + boundaryDSq v := by
  simp only [boundaryDSq, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem boundaryDSq_le_of_hilbert_difference {ι : Type*} [Fintype ι]
    {U : ℝ → EuclideanSpace ℂ ι} {w v : ℝ → ℂ}
    (hU : Continuous U) (hw : Continuous w) (hv : Continuous v)
    (hUp : Function.Periodic U (2 * Real.pi))
    (hwp : Function.Periodic w (2 * Real.pi))
    (hvp : Function.Periodic v (2 * Real.pi))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ θ τ, ‖v θ - v τ‖ ≤ C * (‖U θ - U τ‖ + D * ‖w θ - w τ‖)) :
    boundaryDSq (fun θ (_ : Unit) => v θ) ≤
      ENNReal.ofReal (2 * C ^ 2 * (1 + D ^ 2)) *
        (boundaryDSq (fun θ i => U θ i) + boundaryDSq (fun θ (_ : Unit) => w θ)) := by
  let u : ℝ → (ι ⊕ Unit) → ℂ := fun θ => Sum.elim (fun i => U θ i) (fun _ => w θ)
  have hu (i : ι ⊕ Unit) : Continuous (fun θ => u θ i) := by
    cases i with
    | inl i => exact (PiLp.continuous_apply 2 (fun _ : ι => ℂ) i).comp hU
    | inr i => exact hw
  have hup (i : ι ⊕ Unit) : Function.Periodic (fun θ => u θ i) (2 * Real.pi) := by
    intro θ
    cases i with
    | inl i => exact congrArg (fun z : EuclideanSpace ℂ ι => z i) (hUp θ)
    | inr i => exact hwp θ
  have hh := boundaryDSq_le_of_sum_square_bound hu hv hup hvp
    (C := 2 * C ^ 2 * (1 + D ^ 2)) (by positivity) (fun θ τ => by
      have hsq := mul_self_le_mul_self (norm_nonneg _) (hb θ τ)
      have halg : (C * (‖U θ - U τ‖ + D * ‖w θ - w τ‖)) ^ 2 ≤
          2 * C ^ 2 * (1 + D ^ 2) * (‖U θ - U τ‖ ^ 2 + ‖w θ - w τ‖ ^ 2) := by
        nlinarith [sq_nonneg (C * (‖U θ - U τ‖ - D * ‖w θ - w τ‖)),
          sq_nonneg (C * D * ‖U θ - U τ‖), sq_nonneg (C * ‖w θ - w τ‖)]
      have hnorm : ‖U θ - U τ‖ ^ 2 = ∑ i, ‖U θ i - U τ i‖ ^ 2 := by
        simpa only [PiLp.sub_apply] using PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℂ) (U θ - U τ)
      have hsum : ∑ i : ι ⊕ Unit, ‖u θ i - u τ i‖ ^ 2 =
          ‖U θ - U τ‖ ^ 2 + ‖w θ - w τ‖ ^ 2 := by
        simp only [u, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
          Finset.univ_unique, Finset.sum_singleton, hnorm]
      rw [hsum]
      nlinarith)
  rw [boundaryDSq_sum_index] at hh
  exact hh

end Yau.Blueprint.V03Proof
