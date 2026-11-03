import Yau.Proofs.F04MonotonePotentialLimit

open Filter Set
open scoped Topology
noncomputable section
namespace Yau.F04Proof

/-- A rho-bounded monotone family has a finite real pointwise limit on
 the closed time slab. No source-uniform linear bound is required. -/
theorem rho_dominated_monotone_limit
    {α : Type*} {S : ℝ} (hS : 0 < S) (ρ : α → ℝ → ℝ) (v : ℕ → α → ℝ → ℝ)
    (hMono : ∀ x t, t ∈ Icc 0 S → Monotone (fun j => v j x t))
    (hBound : ∀ j x t, t ∈ Icc 0 S → 0 ≤ v j x t ∧ v j x t ≤ ρ x t)
    (h0 : ∀ j x, v j x 0 = 0) :
    ∃ z : α → ℝ → ℝ,
      (∀ x t, t ∈ Icc 0 S → Tendsto (fun j => v j x t) atTop (𝓝 (z x t))) ∧
      (∀ x t, t ∈ Icc 0 S → 0 ≤ z x t ∧ z x t ≤ ρ x t) ∧
      (∀ j x t, t ∈ Icc 0 S → v j x t ≤ z x t) ∧ (∀ x, z x 0 = 0) := by
  classical
  let z := fun x t => if t ∈ Icc 0 S then ⨆ j : ℕ, v j x t else 0
  have hBdd (x : α) (t : ℝ) (ht : t ∈ Icc 0 S) : BddAbove (range (fun j => v j x t)) :=
    ⟨ρ x t,fun _ hy => by rcases hy with ⟨j,rfl⟩; exact (hBound j x t ht).2⟩
  have hLe (j : ℕ) (x : α) (t : ℝ) (ht : t ∈ Icc 0 S) : v j x t ≤ z x t := by
    change v j x t ≤ if t ∈ Icc 0 S then ⨆ k : ℕ, v k x t else 0
    rw [if_pos ht]
    exact le_ciSup (hBdd x t ht) j
  refine ⟨z,?_,?_,hLe,?_⟩
  · intro x t ht
    change Tendsto (fun j => v j x t) atTop (𝓝 (if t ∈ Icc 0 S then ⨆ j : ℕ, v j x t else 0))
    rw [if_pos ht]
    exact tendsto_atTop_ciSup (hMono x t ht) (hBdd x t ht)
  · intro x t ht
    refine ⟨(hBound 0 x t ht).1.trans (hLe 0 x t ht),?_⟩
    change (if t ∈ Icc 0 S then ⨆ j : ℕ, v j x t else 0) ≤ ρ x t
    rw [if_pos ht]
    exact ciSup_le (fun j => (hBound j x t ht).2)
  · intro x
    change (if (0 : ℝ) ∈ Icc 0 S then ⨆ j : ℕ, v j x 0 else 0) = 0
    rw [if_pos ⟨le_rfl,hS.le⟩]
    simp only [h0,ciSup_const]

end Yau.F04Proof
