import Yau.Proofs.P06PDETypeTraceJets
import Yau.Blueprint.HodgeContracts

noncomputable section
open Filter Set
open scoped Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Aux.PDETypeTrace
open Yau Yau.Blueprint
variable {n k : ℕ} {M : ComplexManifold n}

 theorem formSmoothInitial_iff_smallJets (U : ℝ → RealForm M k) (A : RealForm M k) :
    FormSmoothInitial U A ↔ U 0 = A ∧ ∀ x I,
      SmallJetsOn (chartTarget x) (fun t w => formComponents (U t) x w I - formComponents A x w I) := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    intro x I K hK hKO j ε hε
    obtain ⟨τ, hτ, hh⟩ := h x K hK hKO j I ε hε
    filter_upwards [Ioo_mem_nhdsGT hτ] with t ht
    exact hh t ht.1 ht.2
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    intro x K hK hKO j I ε hε
    obtain ⟨τ, hτ, hh⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (h x I K hK hKO j ε hε)
    exact ⟨τ, hτ, fun t ht htτ => hh ⟨ht, htτ⟩⟩

theorem scalarSmoothInitial_iff_smallJets (u : ℝ → M.Carrier → ℝ) (f : M.Carrier → ℝ) :
    ScalarSmoothInitial u f ↔ u 0 = f ∧ ∀ x,
      SmallJetsOn (chartTarget x) (fun t w => inChart x (u t) w - inChart x f w) := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    intro x K hK hKO j ε hε
    obtain ⟨τ, hτ, hh⟩ := h x K hK hKO j ε hε
    filter_upwards [Ioo_mem_nhdsGT hτ] with t ht
    exact hh t ht.1 ht.2
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    intro x K hK hKO j ε hε
    obtain ⟨τ, hτ, hh⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (h x K hK hKO j ε hε)
    exact ⟨τ, hτ, fun t ht htτ => hh ⟨ht, htτ⟩⟩

end Yau.NodeProofs.P06Aux.PDETypeTrace
