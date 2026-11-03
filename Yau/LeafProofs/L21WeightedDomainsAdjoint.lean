import Yau.LeafProofs.L21WeightedDomainsAdjointPairings

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem weightedMaximalT_adjoint_graph_formal (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA2 : MatrixSmoothOn A (Metric.ball 0 2))
    (v : (weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).adjoint.domain) :
    ((v : WeightedOneForm n K),(weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).adjoint v) ∈
      (weightedMaximalFormalTstar K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).graph := by
  apply (weightedMaximalFormalTstar_compact_pairing_iff K hK A _ _ _).mpr
  intro ξ
  have hp := LinearPMap.adjoint_isFormalAdjoint
    (weightedMaximalT_domain_dense K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)) v
    (weightedCompactTPoint K hK A (weightedDomains_matrixSmoothOn_ball_one hA2) ξ)
  simpa only [inner_conj_symm,weightedCompactTPoint] using congrArg (starRingEnd ℂ) hp

theorem weightedMaximalFormalTstar_graph_adjoint (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA2 : MatrixSmoothOn A (Metric.ball 0 2))
    {v : WeightedOneForm n K} {g : WeightedScalar n K}
    (hGraph : (v,g) ∈ (weightedMaximalFormalTstar K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).graph) :
    ∃ hv : v ∈ (weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).adjoint.domain,
      (weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).adjoint ⟨v,hv⟩ = g := by
  apply weightedMaximalT_adjoint_of_compact_pairings K hK A hA2 v g
  intro ξ
  have hp := (weightedMaximalFormalTstar_compact_pairing_iff K hK A _ v g).mp hGraph ξ
  simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) hp

/-- Equality of the actual graphs identifies the Hilbert adjoint in both
directions, without any assumed adjoint or domain property. -/
theorem weightedMaximalT_adjoint_graph_eq (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA2 : MatrixSmoothOn A (Metric.ball 0 2)) :
    (weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).adjoint.graph =
      (weightedMaximalFormalTstar K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).graph := by
  ext p
  constructor
  · intro hp
    obtain ⟨v,hv,he⟩ := (LinearPMap.mem_graph_iff _).mp hp
    have hh := weightedMaximalT_adjoint_graph_formal K hK A hA2 v
    simpa only [hv,he] using hh
  · intro hp
    obtain ⟨hv,he⟩ := weightedMaximalFormalTstar_graph_adjoint K hK A hA2 hp
    exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨p.1,hv⟩,rfl,he⟩

end Yau.LeafProofs.L21Aux
