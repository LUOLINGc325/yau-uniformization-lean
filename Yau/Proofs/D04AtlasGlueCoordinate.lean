import Yau.Proofs.D04AtlasGlueCover

open MeasureTheory Filter Set
open scoped Topology Manifold ENNReal

noncomputable section

namespace Yau.Proofs.D04AtlasGlueAux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

/-- Apply the unchanged coordinate bridge in any open connected portion of
any original chart, after any strictly increasing selection. All domains and
all functions are the original ones pulled back by the actual inverse chart. -/
theorem coordinate_extraction
    (hcoord : PshCompactnessBridge n) (a : M.Carrier)
    (D : Set (ComplexVector n)) (hD : IsOpen D) (hconn : IsConnected D)
    (hDt : D ⊆ chartTarget a)
    (Ωs : ℕ → Set M.Carrier) (us : ℕ → M.Carrier → EReal)
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = univ)
    (hpsh : ∀ j, PshOnManifold (us j) (Ωs j))
    (hupper : ∀ K : Set M.Carrier, IsCompact K → ∃ C : ℝ, ∀ j,
      K ⊆ Ωs j → ∀ x ∈ K, us j x ≤ (C : EReal))
    (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧
      (PshCollapses D (fun j z => us (s j) (chartInv a z)) τ ∨
        PshL1Limit D (fun j z => us (s j) (chartInv a z)) τ) := by
  let Λ : ℕ → Set (ComplexVector n) := fun j =>
    D ∩ chartInv a ⁻¹' Ωs (s j)
  have hmono : Monotone Ωs := monotone_nat_of_le_succ (fun j => (hΩ j).2)
  have hΛ : ∀ j, IsOpen (Λ j) ∧ Λ j ⊆ Λ (j + 1) ∧ Λ j ⊆ D := by
    intro j
    refine ⟨?_, ?_, inter_subset_left⟩
    · exact ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono hDt).isOpen_inter_preimage
        hD (hΩ (s j)).1
    · intro z hz
      exact ⟨hz.1, hmono (hs.monotone (Nat.le_succ j)) hz.2⟩
  have hΛcover : (⋃ j, Λ j) = D := by
    apply Subset.antisymm
    · exact iUnion_subset (fun j => (hΛ j).2.2)
    · intro z hz
      have : chartInv a z ∈ ⋃ j, Ωs j := by rw [hcover]; exact mem_univ _
      obtain ⟨j, hj⟩ := mem_iUnion.mp this
      exact mem_iUnion.mpr ⟨j, hz, hmono (hs.id_le j) hj⟩
  have hΛpsh : ∀ j, IsPshOn (fun z => us (s j) (chartInv a z)) (Λ j) := by
    intro j
    exact D04Aux.isPshOn_mono ((hpsh (s j)).2.2 a)
      (fun z hz => ⟨hDt hz.1, hz.2⟩)
  have hΛupper : ∀ K ⊆ D, IsCompact K → ∃ C : ℝ, ∀ j,
      K ⊆ Λ j → ∀ z ∈ K, us (s j) (chartInv a z) ≤ (C : EReal) := by
    intro K hKD hK
    have hiK : IsCompact (chartInv a '' K) :=
      hK.image_of_continuousOn
        ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hKD.trans hDt))
    obtain ⟨C, hC⟩ := hupper _ hiK
    refine ⟨C, ?_⟩
    intro j hj z hz
    apply hC (s j) ?_ (chartInv a z) (mem_image_of_mem _ hz)
    rintro x ⟨w, hw, rfl⟩
    exact (hj hw).2
  obtain ⟨τ, hτ, hbranch, _⟩ :=
    hcoord D hD hconn Λ (fun j z => us (s j) (chartInv a z))
      hΛ hΛcover hΛpsh hΛupper
  exact ⟨τ, hτ, hbranch⟩

end Yau.Proofs.D04AtlasGlueAux
