import Yau.Proofs.P06ExteriorHeatEnergy

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.ExteriorHeat
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

/-- Compact tests characterize the original self-adjoint Hodge graph. -/
theorem hodgeGraph_iff_compact_pairings (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u w : L2FormHilbert g μ k) :
    (u,w) ∈ (hodgeCompleteOperator g μ hμ k).graph ↔
      ∀ (B : RealForm M k) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B),
        inner ℝ u (realizeActualForm g μ (hodgeRealForm g.form k B)
          (hodgeRealForm_l2 g μ hμ B hB hcB)) =
        inner ℝ w (realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)) := by
  rw [hodgeCompleteOperator, hodgeCoreOperator_closure_eq_adjoint,
    LinearPMap.adjoint_graph_eq_graph_adjoint (hodgeCoreOperator_domain_dense g μ hμ k),
    hodgeCoreOperator_graph, Submodule.mem_adjoint_iff]
  constructor
  · intro h B hB hcB
    have hc := hodgeRealForm_corePair g μ hμ B hB hcB
    have he := h _ _ (show (realizeActualForm g μ B _,
      realizeActualForm g μ (hodgeRealForm g.form k B) _) ∈
        hodgeCoreGraphSubmodule g μ hμ k from ⟨B,_,hc,rfl⟩)
    simpa only [real_inner_comm] using sub_eq_zero.mp he
  · intro h a b hab
    obtain ⟨B,Z,hc,heq⟩ := hab
    have hz := ((hodgeCorePair_iff_computed g μ hμ B Z).mp hc).2.2
    have he := h B hc.1 hc.2.1
    rw [← realizeActualForm_congr g μ Z (hodgeRealForm g.form k B)
      hc.2.2.2.2.1 (hodgeRealForm_l2 g μ hμ B hc.1 hc.2.1) hz] at he
    have he' : inner ℝ a w = inner ℝ b u := by
      have ha := congrArg Prod.fst heq
      have hb := congrArg Prod.snd heq
      dsimp at ha hb
      rw [ha,hb]
      simpa only [real_inner_comm,realizeActualForm] using he.symm
    exact sub_eq_zero.mpr he'.symm

theorem hodgeGraph_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u w : L2FormHilbert g μ k}
    (hu : (u,w) ∈ (hodgeCompleteOperator g μ hμ k).graph)
    (B : RealForm M k) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    inner ℝ u (realizeActualForm g μ (hodgeRealForm g.form k B) (hodgeRealForm_l2 g μ hμ B hB hcB)) =
      inner ℝ w (realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)) :=
  (hodgeGraph_iff_compact_pairings g μ hμ u w).mp hu B hB hcB

theorem hodgeGraph_of_compact_pairings (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u w : L2FormHilbert g μ k)
    (hp : ∀ (B : RealForm M k) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B),
      inner ℝ u (realizeActualForm g μ (hodgeRealForm g.form k B) (hodgeRealForm_l2 g μ hμ B hB hcB)) =
      inner ℝ w (realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB))) :
    (u,w) ∈ (hodgeCompleteOperator g μ hμ k).graph :=
  (hodgeGraph_iff_compact_pairings g μ hμ u w).mpr hp

/-- Genuine unbounded d intertwines the original adjacent-degree resolvents. -/
theorem exteriorGraph_resolvent (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {f : L2FormHilbert g μ k}
    {df : L2FormHilbert g μ (k+1)} (hdf : (f,df) ∈ (closedExterior g μ hμ k).graph)
    (s : ℝ) (hs : 0 < s) :
    (hodgeImplicitResolvent g μ hμ k s hs f,
      hodgeImplicitResolvent g μ hμ (k+1) s hs df) ∈ (closedExterior g μ hμ k).graph := by
  let u := hodgeImplicitResolvent g μ hμ k s hs f
  let w := s⁻¹ • (f-u)
  have huw : (u,w) ∈ (hodgeCompleteOperator g μ hμ k).graph :=
    hodgeImplicitResolvent_graph g μ hμ k s hs f
  obtain ⟨v,huv,_⟩ := hodgeGraph_exterior g μ hμ huw
  have hvT : (v,s⁻¹ • (df-v)) ∈ (hodgeCompleteOperator g μ hμ (k+1)).graph := by
    apply hodgeGraph_of_compact_pairings g μ hμ
    intro B hB hcB
    have hHB := hodgeRealForm_smooth g μ hμ B hB
    have hcHB := hodgeRealForm_compactlySupported g μ hμ B hB hcB
    have hδB := codifferentialRealForm_smooth g μ hμ B hB
    have hcδB := codifferentialRealForm_compactlySupported g μ hμ B hB hcB
    have he := exteriorGraph_pairing g μ hμ huv (hodgeRealForm g.form (k+1) B) hHB hcHB
    have hc := codifferential_hodge_commute g μ hμ B hB
    rw [show realizeActualForm g μ (codifferentialRealForm g.form (hodgeRealForm g.form (k+1) B)) _ =
      realizeActualForm g μ (hodgeRealForm g.form k (codifferentialRealForm g.form B))
        (hodgeRealForm_l2 g μ hμ _ hδB hcδB) from
        realizeActualForm_congr g μ _ _ _ _ hc] at he
    rw [hodgeGraph_pairing g μ hμ huw _ hδB hcδB] at he
    have hd := exteriorGraph_pairing g μ hμ hdf B hB hcB
    have hv := exteriorGraph_pairing g μ hμ huv B hB hcB
    rw [he]
    simp only [w, real_inner_smul_left, inner_sub_left]
    rw [← hd, ← hv]
  have heq : v = hodgeImplicitResolvent g μ hμ (k+1) s hs df := by
    apply positiveShift_graph_injective (hodgeCompleteOperator g μ hμ (k+1))
      (hodgeCompleteOperator_nonnegative g μ hμ (k+1)) (inv_pos.mpr hs) hvT
      (hodgeImplicitResolvent_graph g μ hμ (k+1) s hs df)
    module
  simpa only [heq] using huv

end Yau.NodeProofs.P06Aux.ExteriorHeat
