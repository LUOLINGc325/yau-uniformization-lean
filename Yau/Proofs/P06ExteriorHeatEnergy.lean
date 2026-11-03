import Yau.Proofs.P06ExteriorHeatGraph
import Yau.LeafProofs.L03CutoffEnergyLimits

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.ExteriorHeat
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

/-- All degrees use the actual zero/successor Hodge energy identities. -/
theorem exteriorCore_energy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    ‖realizeActualForm g μ (exteriorRealForm A) (exteriorRealForm_l2 g μ hμ A hA hcA)‖ ^ 2 ≤
      inner ℝ (realizeActualForm g μ A (smooth_compactlySupported_l2RealForm g μ hμ A hA hcA))
        (realizeActualForm g μ (hodgeRealForm g.form k A) (hodgeRealForm_l2 g μ hμ A hA hcA)) := by
  rw [realizeActualForm_norm_sq, real_inner_comm, realizeActualForm_inner]
  cases k with
  | zero =>
    have he := integral_hodgeRealForm_zero_energy g μ hμ A A hA hA hcA
    simpa only [formNormSq] using he.ge
  | succ k =>
    have he := integral_hodgeRealForm_succ_energy g μ hμ A A hA hA hcA hcA
    rw [he]
    have hn : 0 ≤ ∫ y, formNormSq g.form (codifferentialRealForm g.form A) y ∂μ :=
      integral_nonneg (fun y => formNormSq_nonneg g.form _ y)
    simpa only [formNormSq] using le_add_of_nonneg_left hn

theorem exteriorCore_graph_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W : RealForm M k)
    (hc : OperatorCandidates.HodgeCorePair g.form μ A W) :
    ‖realizeActualForm g μ (exteriorRealForm A) (exteriorRealForm_l2 g μ hμ A hc.1 hc.2.1)‖ ≤
      ‖realizeActualForm g μ A hc.2.2.2.1‖ + ‖realizeActualForm g μ W hc.2.2.2.2.1‖ := by
  have hW := ((hodgeCorePair_iff_computed g μ hμ A W).mp hc).2.2
  have he := exteriorCore_energy g μ hμ A hc.1 hc.2.1
  rw [← realizeActualForm_congr g μ W (hodgeRealForm g.form k A)
    hc.2.2.2.2.1 (hodgeRealForm_l2 g μ hμ A hc.1 hc.2.1) hW] at he
  have hcs := real_inner_le_norm (realizeActualForm g μ A hc.2.2.2.1)
    (realizeActualForm g μ W hc.2.2.2.2.1)
  have hd0 := norm_nonneg (realizeActualForm g μ (exteriorRealForm A)
    (exteriorRealForm_l2 g μ hμ A hc.1 hc.2.1))
  have ha0 := norm_nonneg (realizeActualForm g μ A hc.2.2.2.1)
  have hw0 := norm_nonneg (realizeActualForm g μ W hc.2.2.2.2.1)
  nlinarith [sq_nonneg (‖realizeActualForm g μ A hc.2.2.2.1‖ -
    ‖realizeActualForm g μ W hc.2.2.2.2.1‖)]

theorem exteriorCore_derivatives_cauchy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (As Ws : ℕ → RealForm M k)
    (hc : ∀ j, OperatorCandidates.HodgeCorePair g.form μ (As j) (Ws j))
    (hA : CauchySeq (fun j => realizeActualForm g μ (As j) (hc j).2.2.2.1))
    (hW : CauchySeq (fun j => realizeActualForm g μ (Ws j) (hc j).2.2.2.2.1)) :
    CauchySeq (fun j => realizeActualForm g μ (exteriorRealForm (As j))
      (exteriorRealForm_l2 g μ hμ _ (hc j).1 (hc j).2.1)) := by
  apply cauchySeq_of_two_dist_bound _ _ _ hA hW 1 1 zero_le_one zero_le_one
  intro i j
  have hsub : OperatorCandidates.HodgeCorePair g.form μ (As i - As j) (Ws i - Ws j) := by
    simpa only [neg_one_smul ℝ (As j), neg_one_smul ℝ (Ws j), ← sub_eq_add_neg] using
      hodgeCorePair_add g μ hμ (hc i) (hodgeCorePair_smul g μ hμ (-1) (hc j))
  have hb := exteriorCore_graph_bound g μ hμ _ _ hsub
  simp only [dist_eq_norm, one_mul]
  rw [← realizeActualForm_sub, ← realizeActualForm_sub, ← realizeActualForm_sub]
  simpa only [exteriorRealForm_sub (As i) (As j) (hc i).1 (hc j).1] using hb

/-- The original Hodge closure graph lies in the genuine closed d domain. -/
theorem hodgeGraph_exterior (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u w : L2FormHilbert g μ k}
    (huw : (u,w) ∈ (hodgeCompleteOperator g μ hμ k).graph) :
    ∃ v : L2FormHilbert g μ (k+1), (u,v) ∈ (closedExterior g μ hμ k).graph ∧
      ‖v‖ ^ 2 ≤ inner ℝ u w := by
  classical
  have hcl : (u,w) ∈ closure (hodgeCoreRealizedGraph g μ k) := by
    change (u,w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph at huw
    rw [← (hodgeCoreOperator_closable g μ hμ k).graph_closure_eq_closure_graph,
      hodgeCoreOperator_graph] at huw
    exact huw
  obtain ⟨p, hp, ht⟩ := mem_closure_iff_seq_limit.mp hcl
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
    (exteriorCore_derivatives_cauchy g μ hμ As Ws hc hu.cauchySeq hw.cauchySeq)
  refine ⟨v, ?_, ?_⟩
  · apply (closedExterior_isClosed g μ hμ k).mem_of_tendsto (hu.prodMk_nhds hv)
    exact Eventually.of_forall fun j => exteriorGraph_core g μ hμ (As j) (hc j).1 (hc j).2.1
  · apply le_of_tendsto_of_tendsto (hv.norm.pow 2) (hu.inner hw)
    exact Eventually.of_forall fun j => by
      have he := exteriorCore_energy g μ hμ (As j) (hc j).1 (hc j).2.1
      have hW := ((hodgeCorePair_iff_computed g μ hμ _ _).mp (hc j)).2.2
      rw [← realizeActualForm_congr g μ (Ws j) (hodgeRealForm g.form k (As j))
        (hc j).2.2.2.2.1 (hodgeRealForm_l2 g μ hμ (As j) (hc j).1 (hc j).2.1) hW] at he
      exact he

end Yau.NodeProofs.P06Aux.ExteriorHeat
