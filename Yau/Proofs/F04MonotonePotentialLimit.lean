import Yau.Proofs.F04PotentialCutoffs

open Filter Set
open scoped Topology
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- The pointwise supremum of actual bounded monotone potentials is a
 finite real function, with the SAME rho and linear-time bounds. The
 convergence is proved at every closed time, including the zero face. -/
theorem monotone_potential_limit
    {n : ℕ} (X : KahlerManifold n) {T M : ℝ} (hT : 0 < T)
    (ρ : STF X) (v : ℕ → STF X)
    (hMono : ∀ x t, t ∈ Icc 0 T → Monotone (fun j => v j x t))
    (hBound : ∀ j x t, t ∈ Icc 0 T → 0 ≤ v j x t ∧ v j x t ≤ ρ x t ∧ v j x t ≤ M*t)
    (h0 : ∀ j x, v j x 0 = 0) :
    ∃ z : STF X,
      (∀ x t, t ∈ Icc 0 T → Tendsto (fun j => v j x t) atTop (𝓝 (z x t))) ∧
      (∀ x t, t ∈ Icc 0 T → 0 ≤ z x t ∧ z x t ≤ ρ x t ∧ z x t ≤ M*t) ∧
      (∀ j x t, t ∈ Icc 0 T → v j x t ≤ z x t) ∧
      (∀ x, z x 0 = 0) := by
  classical
  let z : STF X := fun x t => if t ∈ Icc 0 T then ⨆ j : ℕ, v j x t else 0
  have hBdd (x : Pt X) (t : ℝ) (ht : t ∈ Icc 0 T) : BddAbove (range (fun j => v j x t)) :=
    ⟨ρ x t,fun _ hy => by rcases hy with ⟨j,rfl⟩; exact (hBound j x t ht).2.1⟩
  have hLe (j : ℕ) (x : Pt X) (t : ℝ) (ht : t ∈ Icc 0 T) : v j x t ≤ z x t := by
    change v j x t ≤ if t ∈ Icc 0 T then ⨆ k : ℕ, v k x t else 0
    rw [if_pos ht]
    exact le_ciSup (hBdd x t ht) j
  refine ⟨z,?_,?_,hLe,?_⟩
  · intro x t ht
    change Tendsto (fun j => v j x t) atTop (𝓝 (if t ∈ Icc 0 T then ⨆ j : ℕ, v j x t else 0))
    rw [if_pos ht]
    exact tendsto_atTop_ciSup (hMono x t ht) (hBdd x t ht)
  · intro x t ht
    have hNonneg : 0 ≤ z x t := (hBound 0 x t ht).1.trans (hLe 0 x t ht)
    have hUpper : z x t ≤ ρ x t := by
      change (if t ∈ Icc 0 T then ⨆ j : ℕ, v j x t else 0) ≤ ρ x t
      rw [if_pos ht]
      exact ciSup_le (fun j => (hBound j x t ht).2.1)
    have hLinear : z x t ≤ M*t := by
      change (if t ∈ Icc 0 T then ⨆ j : ℕ, v j x t else 0) ≤ M*t
      rw [if_pos ht]
      exact ciSup_le (fun j => (hBound j x t ht).2.2)
    exact ⟨hNonneg,hUpper,hLinear⟩
  · intro x
    change (if (0 : ℝ) ∈ Icc 0 T then ⨆ j : ℕ, v j x 0 else 0) = 0
    rw [if_pos ⟨le_rfl,hT.le⟩]
    simp only [h0,ciSup_const]

end Yau.F04Proof
