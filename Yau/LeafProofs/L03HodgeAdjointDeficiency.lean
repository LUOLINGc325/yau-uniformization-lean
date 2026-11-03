import Yau.LeafProofs.L03CompletionRepresentatives
import Yau.LeafProofs.L03HodgeDeficiency

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- The actual Hilbert adjoint has no negative-one deficiency vector.
Completion vectors are first represented by genuine measurable L²
sections, then the proved original raw maximal equation is used. -/
theorem hodgeCoreOperator_adjoint_neg_self_eq_zero
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ℕ) (u : (hodgeCoreOperator g μ hμ k).adjoint.domain)
    (hu : (hodgeCoreOperator g μ hμ k).adjoint u = -(u : L2FormHilbert g μ k)) :
    (u : L2FormHilbert g μ k) = 0 := by
  obtain ⟨A, hA, heA⟩ := l2FormHilbert_exists_section g μ (u : L2FormHilbert g μ k)
  have hnegA : L2RealForm g.form μ (-A) := (l2FormSubmodule g μ k).neg_mem hA
  have heneg : realizeL2Form g μ (L2FormSpace.ofSection (-A) hnegA) = -(u : L2FormHilbert g μ k) :=
    (UniformSpace.Completion.coe_neg (L2FormSpace.ofSection A hA)).trans (congrArg Neg.neg heA)
  have hgraph : ((u : L2FormHilbert g μ k), (hodgeCoreOperator g μ hμ k).adjoint u) ∈
      (hodgeCoreOperator g μ hμ k).adjoint.graph := by
    rw [LinearPMap.mem_graph_iff]
    exact ⟨u, rfl, rfl⟩
  have hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A (-A) :=
    (hodgeMaximalGraph_iff_operator_adjoint g μ hμ A (-A) hA hnegA).mpr (by
      rw [heA, heneg, ← hu]
      exact hgraph)
  have hzero := hodgeMaximalGraph_neg_self_ae_zero g μ hμ A hmax
  have hezero : realizeL2Form g μ (L2FormSpace.ofSection A hA) = 0 :=
    (realizeL2Form_eq_iff_ae g μ (L2FormSpace.ofSection A hA) 0).mpr hzero
  exact heA.symm.trans hezero

end Yau.LeafProofs.L03
