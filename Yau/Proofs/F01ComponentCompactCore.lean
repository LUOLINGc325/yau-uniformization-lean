import Yau.Proofs.F01SublevelTopology

/-! A compact set lying strictly inside an open sublevel has compact
intersection with its actual base-point component. -/
noncomputable section
open Set Topology
namespace Yau.NodeProofs.F01Aux
variable {A : Type*} [TopologicalSpace A]

theorem isCompact_connectedComponentIn_inter {U K : Set A} (o : A)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    IsCompact (connectedComponentIn U o ∩ K) := by
  by_cases ho : o ∈ U
  · have hrel : IsClosed ((Subtype.val : U → A) ⁻¹' connectedComponentIn U o) := by
      rw [connectedComponentIn_eq_image ho]
      simpa only [preimage_image_eq _ Subtype.val_injective] using
        (isClosed_connectedComponent (x := (⟨o, ho⟩ : U)))
    obtain ⟨F, hF, heq⟩ := IsInducing.subtypeVal.isClosed_iff.mp hrel
    have hsets : connectedComponentIn U o ∩ K = F ∩ K := by
      ext x
      constructor
      · intro hx
        have hu : x ∈ U := connectedComponentIn_subset U o hx.1
        have hh := Set.ext_iff.mp heq (⟨x, hu⟩ : U)
        exact ⟨hh.mpr hx.1, hx.2⟩
      · intro hx
        have hu := hKU hx.2
        have hh := Set.ext_iff.mp heq (⟨x, hu⟩ : U)
        exact ⟨hh.mp hx.1, hx.2⟩
    rw [hsets]
    exact hK.inter_left hF
  · rw [connectedComponentIn_eq_empty ho, empty_inter]
    exact isCompact_empty

end Yau.NodeProofs.F01Aux
