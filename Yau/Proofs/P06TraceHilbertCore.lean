import Yau.Proofs.P06TraceHilbertMaps
import Yau.Proofs.P06HodgeOperator

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.TraceHilbert
open Yau Yau.LeafProofs Yau.LeafProofs.L03 G04Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The full degree-two core is first projected to its actual (1,1) part.
The anti-(1,1) component has zero contraction with the Kähler form. -/
theorem corePair_contraction (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    {A W : RealForm M 2} (hAW : OperatorCandidates.HodgeCorePair g.form μ A W) :
    OperatorCandidates.HodgeCorePair g.form μ
      (fiberContraction g.form (omegaForm g.form) A)
      (fiberContraction g.form (omegaForm g.form) W) := by
  have hp := P06Weitzenbock.hodgeCorePair_projection g μ hμ hk hAW
  have ht := P06Weitzenbock.hodgeCorePair_trace g μ hμ hk hp
    (P06Weitzenbock.oneOneProjection_type A)
  rw [← contraction_eq_trace _ _ (P06Weitzenbock.oneOneProjection_type A),
    ← contraction_eq_trace _ _ (P06Weitzenbock.oneOneProjection_type W),
    contraction_projection, contraction_projection] at ht
  exact ht

theorem core_graph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    {u w : L2FormHilbert g μ 2} (huw : (u, w) ∈ (hodgeCoreOperator g μ hμ 2).graph) :
    (contraction g μ u, contraction g μ w) ∈ (hodgeCoreOperator g μ hμ 0).graph := by
  rw [hodgeCoreOperator_graph] at huw ⊢
  obtain ⟨A, W, hAW, he⟩ := huw
  have ht := corePair_contraction g μ hμ hk hAW
  have hu := congrArg Prod.fst he
  have hw := congrArg Prod.snd he
  change u = _ at hu
  change w = _ at hw
  rw [hu, hw]
  refine ⟨_, _, ht, ?_⟩
  exact Prod.ext (contraction_realize g μ A hAW.2.2.2.1)
    (contraction_realize g μ W hAW.2.2.2.2.1)

theorem closed_graph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    {u w : L2FormHilbert g μ 2}
    (huw : (u, w) ∈ (hodgeCoreOperator g μ hμ 2).closure.graph) :
    (contraction g μ u, contraction g μ w) ∈
      (hodgeCoreOperator g μ hμ 0).closure.graph := by
  let F : L2FormHilbert g μ 2 × L2FormHilbert g μ 2 →
      L2FormHilbert g μ 0 × L2FormHilbert g μ 0 :=
    fun p => (contraction g μ p.1, contraction g μ p.2)
  have hc : IsClosed (F ⁻¹' ((hodgeCoreOperator g μ hμ 0).closure.graph : Set _)) :=
    (hodgeCoreOperator_closable g μ hμ 0).closure_isClosed.preimage
      (((contraction g μ).continuous.comp continuous_fst).prodMk
        ((contraction g μ).continuous.comp continuous_snd))
  have hi : ((hodgeCoreOperator g μ hμ 2).graph : Set _) ⊆
      F ⁻¹' ((hodgeCoreOperator g μ hμ 0).closure.graph : Set _) := by
    intro p hp
    exact LinearPMap.le_graph_of_le (hodgeCoreOperator g μ hμ 0).le_closure
      (core_graph g μ hμ hk hp)
  have hu : (u, w) ∈ closure ((hodgeCoreOperator g μ hμ 2).graph : Set _) := by
    rw [← Submodule.topologicalClosure_coe,
      (hodgeCoreOperator_closable g μ hμ 2).graph_closure_eq_closure_graph]
    exact huw
  exact closure_minimal hi hc hu

end Yau.NodeProofs.P06Aux.TraceHilbert
