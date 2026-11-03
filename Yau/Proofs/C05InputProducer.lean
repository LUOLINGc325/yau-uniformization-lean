import Yau.Blueprint.Nodes

/-! The four original predecessors supply the same-manifold inlet of C05. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C05Aux

open Yau Yau.Blueprint

theorem C05_input_producer_of_original_predecessors
    (hF01 : F01) (hF04 : F04) (hC01 : C01) (hC04 : C04) : C05InputProducer := by
  intro n X o
  obtain ⟨h, U, P, ρ, hlocalized⟩ := hF01 n X o
  exact ⟨h, U, P, ρ, ⟨hlocalized, hF04 n X o h U P ρ hlocalized⟩,
    hC01 n X o h U P ρ hlocalized, hC04 n X o h U P ρ hlocalized⟩

end Yau.Proofs.C05Aux
