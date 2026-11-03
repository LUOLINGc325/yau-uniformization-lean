import Yau.Proofs.D04CoordinateCompactness
import Yau.Proofs.D04CoordinateAnchors

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

/-- The original arbitrary-dimensional coordinate compactness bridge, with
actual exhausting domains, both alternatives and both lower-anchor clauses. -/
theorem coordinate_psh_compactness (n : ℕ) : PshCompactnessBridge n := by
  intro D hD hconn Ωs us hΩ hcover hpsh hupper
  have hmono : Monotone Ωs := monotone_nat_of_le_succ (fun j => (hΩ j).2.1)
  have hfinish (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (halt : PshCollapses D us φ ∨ PshL1Limit D us φ) :
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        (PshCollapses D us phi ∨ PshL1Limit D us phi) ∧
        (∀ (K : Set (ComplexVector n)) (z : ℕ → ComplexVector n) (A : ℝ),
          IsCompact K → K ⊆ D → (∀ j, z j ∈ K ∧ z j ∈ Ωs (phi j) ∧
            ((-A : ℝ) : EReal) ≤ us (phi j) (z j)) → ¬ PshCollapses D us phi) ∧
        (∀ (K : Set (ComplexVector n)) (Es : ℕ → Set (ComplexVector n)) (A c : ℝ),
          IsCompact K → K ⊆ D → 0 < c →
          (∀ j, MeasurableSet (Es j) ∧ Es j ⊆ K ∩ Ωs (phi j) ∧
            ENNReal.ofReal c ≤ lebesgueC n (Es j) ∧
            ∀ x ∈ Es j, ((-A : ℝ) : EReal) ≤ us (phi j) x) → ¬ PshCollapses D us phi) := by
    refine ⟨φ, hφ, halt, ?_, ?_⟩
    · intro K z A hK hKD hz
      exact not_pshCollapses_of_point_anchor hK hKD (fun j => ⟨(hz j).1, (hz j).2.2⟩)
    · intro K Es A c hK hKD hc hEs
      exact not_pshCollapses_of_positive_measure_anchor hK hKD hc
        (fun j => ⟨(hEs j).2.1.trans inter_subset_left, (hEs j).2.2.1, (hEs j).2.2.2⟩)
  rcases coordinate_collapse_or_point_anchored_subsequence hΩ hcover with hcollapse |
    ⟨φ₁, K, z, A, hφ₁, hK, hKD, hanchor⟩
  · exact hfinish id strictMono_id (Or.inl hcollapse)
  · let Ω₁ : ℕ → Set (ComplexVector n) := fun j => Ωs (φ₁ j)
    let u₁ : ℕ → ComplexVector n → EReal := fun j => us (φ₁ j)
    have hΩ₁ : ∀ j, IsOpen (Ω₁ j) ∧ Ω₁ j ⊆ Ω₁ (j + 1) ∧ Ω₁ j ⊆ D :=
      fun j => ⟨(hΩ (φ₁ j)).1, hmono (hφ₁.monotone (Nat.le_succ j)), (hΩ (φ₁ j)).2.2⟩
    have hcover₁ : (⋃ j, Ω₁ j) = D := by
      apply Subset.antisymm
      · intro x hx
        obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        exact (hΩ (φ₁ j)).2.2 hj
      · intro x hx
        rw [← hcover] at hx
        obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨j, hmono (hφ₁.id_le j) hj⟩
    have hpsh₁ : ∀ j, IsPshOn (u₁ j) (Ω₁ j) := fun j => hpsh (φ₁ j)
    have hupper₁ : ∀ T ⊆ D, IsCompact T → ∃ C : ℝ, ∀ j,
        T ⊆ Ω₁ j → ∀ y ∈ T, u₁ j y ≤ (C : EReal) := by
      intro T hTD hT
      obtain ⟨C, hC⟩ := hupper T hTD hT
      exact ⟨C, fun j => hC (φ₁ j)⟩
    obtain ⟨ψ, hψ, htail⟩ := uniform_localL1_of_moving_anchor D hD hconn Ω₁ u₁ hΩ₁ hcover₁
      hpsh₁ hupper₁ K z A hK hKD hanchor
    let Ω₂ : ℕ → Set (ComplexVector n) := fun j => Ω₁ (ψ j)
    let u₂ : ℕ → ComplexVector n → EReal := fun j => u₁ (ψ j)
    obtain ⟨χ, hχ, hlim⟩ := pshL1Limit_of_eventual_localL1 hD hconn.nonempty Ω₂ u₂
      (fun j => hpsh₁ (ψ j)) (fun T hT hTD => htail T hTD hT)
    let φ : ℕ → ℕ := φ₁ ∘ ψ ∘ χ
    have hφ : StrictMono φ := hφ₁.comp (hψ.comp hχ)
    have hlimOriginal : PshL1Limit D us φ := by
      simpa only [PshL1Limit, u₂, u₁, φ, Function.comp_def] using hlim
    exact hfinish φ hφ (Or.inr hlimOriginal)

end Yau.Proofs.D04Aux
