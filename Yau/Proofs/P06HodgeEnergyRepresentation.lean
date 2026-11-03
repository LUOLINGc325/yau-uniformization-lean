import Yau.Proofs.P06HodgeEnergyGraph
import Yau.Proofs.P06HodgeOperator

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem hodgeEnergy_exists_actual (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u : HodgeEnergySpace g μ hμ) :
    ∃ (A : RealForm M 2) (dA : RealForm M 3) (δA : RealForm M 1),
      ∃ (hA : L2RealForm g.form μ A) (hdA : L2RealForm g.form μ dA) (hδA : L2RealForm g.form μ δA),
      HodgeFormGraphClosure g.form μ A dA δA ∧
      realizeActualForm g μ A hA = hodgeEnergyValue g μ hμ u ∧
      realizeActualForm g μ dA hdA = hodgeEnergyExterior g μ hμ u ∧
      realizeActualForm g μ δA hδA = hodgeEnergyLower g μ hμ u := by
  obtain ⟨A, hA, heA⟩ := l2FormHilbert_exists_section g μ (hodgeEnergyValue g μ hμ u)
  obtain ⟨dA, hdA, hed⟩ := l2FormHilbert_exists_section g μ (hodgeEnergyExterior g μ hμ u)
  obtain ⟨δA, hδA, heδ⟩ := l2FormHilbert_exists_section g μ (hodgeEnergyLower g μ hμ u)
  have he : hodgeEnergyActualTuple g μ A dA δA hA hdA hδA = (u : HodgeEnergyAmbient g μ) := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact heA
    · apply WithLp.ofLp_injective 2
      exact Prod.ext hed heδ
  refine ⟨A, dA, δA, hA, hdA, hδA, ?_, heA, hed, heδ⟩
  apply (hodgeEnergyActualTuple_mem_iff g μ hμ A dA δA hA hdA hδA).mp
  rw [he]
  exact u.property

def hodgeEnergyOfGraph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2) (dA : RealForm M 3) (δA : RealForm M 1)
    (h : HodgeFormGraphClosure g.form μ A dA δA) : HodgeEnergySpace g μ hμ :=
  ⟨hodgeEnergyActualTuple g μ A dA δA h.1 h.2.1 h.2.2.1,
    (hodgeEnergyActualTuple_mem_iff g μ hμ A dA δA h.1 h.2.1 h.2.2.1).mpr h⟩

/-- The same original closed Hodge operator has the genuine d/δ
variational identity in the represented energy Hilbert space. -/
theorem hodgeCompleteGraph_energy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {f w : L2FormHilbert g μ 2}
    (h : (f, w) ∈ (hodgeCompleteOperator g μ hμ 2).graph) :
    ∃ u : HodgeEnergySpace g μ hμ, hodgeEnergyValue g μ hμ u = f ∧
      ∀ v : HodgeEnergySpace g μ hμ,
        hodgeEnergyPairing g μ hμ u v = inner ℝ w (hodgeEnergyValue g μ hμ v) := by
  obtain ⟨A, hA, heA⟩ := l2FormHilbert_exists_section g μ f
  obtain ⟨W, hW, heW⟩ := l2FormHilbert_exists_section g μ w
  change realizeActualForm g μ A hA = f at heA
  change realizeActualForm g μ W hW = w at heW
  have hmin : OperatorCandidates.HodgeMinimalGraph g.form μ A W := by
    apply (hodgeMinimalGraph_iff_operator_closure g μ hμ A W hA hW).mpr
    change (realizeActualForm g μ A hA, realizeActualForm g μ W hW) ∈ _
    rw [heA, heW]
    exact h
  obtain ⟨_, dA, δA, hgraph, hvar⟩ := hodgeMinimalGraph_friedrichs g μ hμ hmin
  let u := hodgeEnergyOfGraph g μ hμ A dA δA hgraph
  refine ⟨u, heA, ?_⟩
  intro v
  obtain ⟨V, dV, δV, hV, hdV, hδV, hgv, heV, hedV, heδV⟩ := hodgeEnergy_exists_actual g μ hμ v
  have hv := hvar V dV δV hgv
  change inner ℝ (realizeActualForm g μ dA hgraph.2.1) (hodgeEnergyExterior g μ hμ v) +
    inner ℝ (realizeActualForm g μ δA hgraph.2.2.1) (hodgeEnergyLower g μ hμ v) = _
  rw [← hedV, ← heδV, ← heV, ← heW, realizeActualForm_inner, realizeActualForm_inner,
    realizeActualForm_inner]
  exact hv.2.2.2

end Yau.NodeProofs.P06Aux
