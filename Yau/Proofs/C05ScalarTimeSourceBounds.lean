import Yau.Proofs.C05ScalarTimeSourceBoundsZeroth

/-! Three explicit budgets for the actual intrinsic scalar evolution sources. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05ScalarTimeSourceBoundsAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
variable {n : ℕ} {M : ComplexManifold n}

theorem scalar_time_sources_bounds (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (x : M.Carrier) {B : ℝ} (hB : 0 ≤ B)
    (hScalar : ∀ j ≤ 6, scalarJetNorm k (scalarCurvature k) j x ≤ B)
    (hRicci : ∀ j ≤ 4, realRicciJetNorm k j x ≤ B) :
    0 ≤ b1 n B ∧ 0 ≤ b2 n B ∧ 0 ≤ b3 n B ∧
    (∀ m ≤ 4, scalarJetNorm k (scalarTimeSource1 k) m x ≤ b1 n B) ∧
    (∀ m ≤ 2, scalarJetNorm k (scalarTimeSource2 k) m x ≤ b2 n B) ∧
    |scalarTimeSource3 k x| ≤ b3 n B :=
  ⟨b1_nonneg n hB, b2_nonneg n hB, b3_nonneg n hB,
    (fun m hm => source1_jet_bound k hk hK m hm x hB hScalar hRicci),
    (fun m hm => source2_jet_bound k hk hK m hm x hB hScalar hRicci),
    source3_abs_bound k hk hK x hB hScalar hRicci⟩

end Yau.Proofs.C05ScalarTimeSourceBoundsAux
