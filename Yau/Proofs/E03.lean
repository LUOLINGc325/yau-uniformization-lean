import Yau.Proofs.E03JointLevi

/-! The original E03 node from precisely its three registered parent contracts. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs
open Yau Yau.Blueprint Yau.BlueprintContracts E03Aux

theorem E03_proved : E01_contract → E02_contract → F04_contract → E03_contract := by
  intro hE01 hE02 hF04 n X o h U P ρ hloc
  have hopt := hE01 n X o h U P ρ hloc
  have hcomp := hE02 n X o h U P ρ hloc
  have hscalar := hF04 n X o h U P ρ hloc
  constructor
  · intro c z η w hz
    exact jointNorm_levi_posSemidef o h U P ρ hloc hopt hcomp hscalar c (z, η, w) hz
  · intro T hT x ξ s hs hsT
    exact envelope_eq_dualNorm o h U P ρ hloc hopt hcomp hscalar T hT x ξ s hs hsT

end Yau.NodeProofs
