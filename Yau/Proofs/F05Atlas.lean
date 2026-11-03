import Yau.Proofs.F05FiniteAtlas
import Yau.Proofs.F05Partition

/-! The finite genuine atlas and its smooth partition are existence outputs
of the original smooth-domain predicate. -/

noncomputable section

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.HeatConcreteBindings Yau.F05Transport

theorem F05_finite_buffered_atlas_partition {n : ℕ} (hn : 0 < n)
    {M : ComplexManifold n} (O : Set M.Carrier) (hO : SmoothPrecompactDomain O) :
    ∃ (A : AtlasData M) (χ : Fin A.count → M.Carrier → ℝ),
      GenuineAtlas O A ∧ F05Partition O A χ ∧
      closure O ⊆ ⋃ i, lift A i '' region (A.normal i) (1/8) := by
  obtain ⟨A,hA,hSmall⟩ := F05_finite_buffered_atlas_core hn O hO
  obtain ⟨χ,hχ⟩ := F05_finite_atlas_partition hO A hA hSmall
  exact ⟨A,χ,hA,hχ,hSmall⟩

theorem F05_finiteAtlasTarget : FiniteAtlasTarget := by
  intro n hn M O hO
  obtain ⟨A,hA,hSmall⟩ := F05_finite_buffered_atlas_core hn O hO
  exact ⟨A,hA⟩

end Yau.Proofs.F05Aux
