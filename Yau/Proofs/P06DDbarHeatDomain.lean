import Yau.Proofs.P06DDbarHeatGraph

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.DDbarHeat
open Yau Yau.LeafProofs Yau.LeafProofs.L03 G04Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem ddForm_core_norm_sq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) (A W : RealForm M 0)
    (hc : OperatorCandidates.HodgeCorePair g.form μ A W) :
    ‖realizeActualForm g μ (ddForm A) (ddForm_l2 g μ hμ A hc.1 hc.2.1)‖ ^ 2 =
      (1/4 : ℝ) * ‖realizeActualForm g μ W hc.2.2.2.2.1‖ ^ 2 := by
  have he := ddCore_norm_sq g μ hμ hk (WeakCurrent.scalarValue A)
    (WeakCurrent.scalarValue_smooth A hc.1) (WeakCurrent.scalarValue_compact A hc.2.1)
  have hW := ((hodgeCorePair_iff_computed g μ hμ A W).mp hc).2.2
  simp only [scalarForm_scalarValue] at he
  rw [realizeActualForm_congr g μ W _ _ _ hW]
  exact he

theorem ddForm_core_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) (A W : RealForm M 0)
    (hc : OperatorCandidates.HodgeCorePair g.form μ A W) :
    ‖realizeActualForm g μ (ddForm A) (ddForm_l2 g μ hμ A hc.1 hc.2.1)‖ ≤
      (1/2 : ℝ) * ‖realizeActualForm g μ W hc.2.2.2.2.1‖ := by
  have he := ddForm_core_norm_sq g μ hμ hk A W hc
  have hd := norm_nonneg (realizeActualForm g μ (ddForm A) (ddForm_l2 g μ hμ A hc.1 hc.2.1))
  have hw := norm_nonneg (realizeActualForm g μ W hc.2.2.2.2.1)
  nlinarith

theorem ddForm_core_cauchy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) (As Ws : ℕ → RealForm M 0)
    (hc : ∀ j, OperatorCandidates.HodgeCorePair g.form μ (As j) (Ws j))
    (hA : CauchySeq (fun j => realizeActualForm g μ (As j) (hc j).2.2.2.1))
    (hW : CauchySeq (fun j => realizeActualForm g μ (Ws j) (hc j).2.2.2.2.1)) :
    CauchySeq (fun j => realizeActualForm g μ (ddForm (As j))
      (ddForm_l2 g μ hμ _ (hc j).1 (hc j).2.1)) := by
  apply cauchySeq_of_two_dist_bound _ _ _ hA hW 0 (1/2) le_rfl (by norm_num)
  intro i j
  have hsub : OperatorCandidates.HodgeCorePair g.form μ (As i - As j) (Ws i - Ws j) := by
    simpa only [neg_one_smul ℝ (As j), neg_one_smul ℝ (Ws j), ← sub_eq_add_neg] using
      hodgeCorePair_add g μ hμ (hc i) (hodgeCorePair_smul g μ hμ (-1) (hc j))
  have hb := ddForm_core_bound g μ hμ hk _ _ hsub
  simp only [dist_eq_norm, zero_mul, zero_add]
  rw [← realizeActualForm_sub, ← realizeActualForm_sub]
  simpa only [ddForm_sub (As i) (As j) (hc i).1 (hc j).1] using hb

/-- A single actual Hodge graph has the actual closed second-order dd realization. -/
theorem hodgeGraph_dd (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) {u w : L2FormHilbert g μ 0}
    (huw : (u,w) ∈ (hodgeCompleteOperator g μ hμ 0).graph) :
    ∃ v : L2FormHilbert g μ 2, (u,v) ∈ (closedDDbar g μ hμ).graph ∧
      ‖v‖ ^ 2 = (1/4 : ℝ) * ‖w‖ ^ 2 := by
  classical
  have hcl : (u,w) ∈ closure (hodgeCoreRealizedGraph g μ 0) := by
    change (u,w) ∈ (hodgeCoreOperator g μ hμ 0).closure.graph at huw
    rw [← (hodgeCoreOperator_closable g μ hμ 0).graph_closure_eq_closure_graph,
      hodgeCoreOperator_graph] at huw
    exact huw
  obtain ⟨p,hp,ht⟩ := mem_closure_iff_seq_limit.mp hcl
  choose As Ws hc heq using hp
  have hu : Tendsto (fun j => realizeActualForm g μ (As j) (hc j).2.2.2.1) atTop (𝓝 u) := by
    have hf := (continuous_fst.tendsto (u,w)).comp ht
    convert hf using 1
    funext j
    exact (congrArg Prod.fst (heq j)).symm
  have hw : Tendsto (fun j => realizeActualForm g μ (Ws j) (hc j).2.2.2.2.1) atTop (𝓝 w) := by
    have hf := (continuous_snd.tendsto (u,w)).comp ht
    convert hf using 1
    funext j
    exact (congrArg Prod.snd (heq j)).symm
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete
    (ddForm_core_cauchy g μ hμ hk As Ws hc hu.cauchySeq hw.cauchySeq)
  refine ⟨v,?_,?_⟩
  · apply (closedDDbar_isClosed g μ hμ).mem_of_tendsto (hu.prodMk_nhds hv)
    exact Eventually.of_forall fun j => ddGraph_core g μ hμ (As j) (hc j).1 (hc j).2.1
  · exact tendsto_nhds_unique (hv.norm.pow 2)
      ((hw.norm.pow 2).const_mul (1/4 : ℝ) |>.congr' (Eventually.of_forall fun j =>
        (ddForm_core_norm_sq g μ hμ hk (As j) (Ws j) (hc j)).symm))

end Yau.NodeProofs.P06Aux.DDbarHeat
