import Yau.Proofs.F05CompactBufferedAtlas

/-! The actual full-raw compact buffers and the original genuine partition
are retained together for fixed reference charts in an exhaustion. -/

noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.HeatConcreteBindings Yau.F05Transport

theorem F05_finite_compact_atlas_partition {n : ℕ} (hn : 0 < n)
    {M : ComplexManifold n} (O : Set M.Carrier) (hO : SmoothPrecompactDomain O) :
    ∃ (A : AtlasData M) (χ : Fin A.count → M.Carrier → ℝ),
      GenuineAtlas O A ∧ F05Partition O A χ ∧
      (closure O ⊆ ⋃ i, lift A i '' region (A.normal i) (1/8)) ∧
      ∀ i, IsCompact (lift A i '' Metric.closedBall 0 3) := by
  obtain ⟨A,hA,hSmall,hCompact⟩ := F05_finite_compact_buffered_atlas hn O hO
  obtain ⟨χ,hχ⟩ := F05_finite_atlas_partition hO A hA hSmall
  exact ⟨A,χ,hA,hχ,hSmall,hCompact⟩

end Yau.Proofs.F05Aux
