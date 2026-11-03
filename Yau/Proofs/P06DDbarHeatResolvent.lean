import Yau.Proofs.P06DDbarHeatTranspose

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.DDbarHeat
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- Actual closed dd intertwines the original degree-zero/two resolvents. -/
theorem ddGraph_resolvent (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) {f : L2FormHilbert g μ 0}
    {df : L2FormHilbert g μ 2} (hdf : (f,df) ∈ (closedDDbar g μ hμ).graph)
    (s : ℝ) (hs : 0 < s) :
    (hodgeImplicitResolvent g μ hμ 0 s hs f,
      hodgeImplicitResolvent g μ hμ 2 s hs df) ∈ (closedDDbar g μ hμ).graph := by
  let u := hodgeImplicitResolvent g μ hμ 0 s hs f
  let w := s⁻¹ • (f-u)
  have huw : (u,w) ∈ (hodgeCompleteOperator g μ hμ 0).graph :=
    hodgeImplicitResolvent_graph g μ hμ 0 s hs f
  obtain ⟨v,huv,_⟩ := hodgeGraph_dd g μ hμ hk huw
  have hvT : (v,s⁻¹ • (df-v)) ∈ (hodgeCompleteOperator g μ hμ 2).graph := by
    apply ExteriorHeat.hodgeGraph_of_compact_pairings g μ hμ
    intro B hB hcB
    have hHB := hodgeRealForm_smooth g μ hμ B hB
    have hcHB := hodgeRealForm_compactlySupported g μ hμ B hB hcB
    have hQB := adjointForm_smooth g μ hμ B hB
    have hcQB := adjointForm_compact g μ hμ B hB hcB
    have he := ddGraph_pairing g μ hμ huv (hodgeRealForm g.form 2 B) hHB hcHB
    rw [adjoint_hodge g μ hμ hk B hB hcB] at he
    rw [ExteriorHeat.hodgeGraph_pairing g μ hμ huw _ hQB hcQB] at he
    have hd := ddGraph_pairing g μ hμ hdf B hB hcB
    have hv := ddGraph_pairing g μ hμ huv B hB hcB
    rw [he]
    simp only [w, real_inner_smul_left, inner_sub_left]
    rw [← hd, ← hv]
  have heq : v = hodgeImplicitResolvent g μ hμ 2 s hs df := by
    apply positiveShift_graph_injective (hodgeCompleteOperator g μ hμ 2)
      (hodgeCompleteOperator_nonnegative g μ hμ 2) (inv_pos.mpr hs) hvT
      (hodgeImplicitResolvent_graph g μ hμ 2 s hs df)
    module
  simpa only [heq] using huv


end Yau.NodeProofs.P06Aux.DDbarHeat
