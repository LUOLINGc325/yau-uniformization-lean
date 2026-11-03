import Yau.Proofs.P06HodgeRegularityCoordinates

/-! The actual closed Hodge graph supplies genuine smooth core pairs and
Hilbert convergence of both entries. Their chart source equations use the
computed all-degree Hodge coefficients. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem hodgeClosureGraph_core_approximation
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : RealForm M k) (hA : L2RealForm g.form μ A) (hW : L2RealForm g.form μ W)
    (hgraph : (realizeActualForm g μ A hA, realizeActualForm g μ W hW) ∈
      (hodgeCoreOperator g μ hμ k).closure.graph) :
    ∃ As Ws : ℕ → RealForm M k, ∃ hc : ∀ m, OperatorCandidates.HodgeCorePair g.form μ (As m) (Ws m),
      Tendsto (fun m => realizeActualForm g μ (As m) (hc m).2.2.2.1) atTop
        (𝓝 (realizeActualForm g μ A hA)) ∧
      Tendsto (fun m => realizeActualForm g μ (Ws m) (hc m).2.2.2.2.1) atTop
        (𝓝 (realizeActualForm g μ W hW)) := by
  obtain ⟨_, _, As, Ws, hc, ht⟩ :=
    (hodgeMinimalGraph_iff_operator_closure g μ hμ A W hA hW).mpr hgraph
  have htA : Tendsto (fun m => formL2DistanceSq g.form μ (As m) A) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => bot_le) (fun _ => le_add_of_nonneg_right (by positivity))
  have htW : Tendsto (fun m => formL2DistanceSq g.form μ (Ws m) W) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => bot_le) (fun _ => le_add_of_nonneg_left (by positivity))
  refine ⟨As, Ws, hc, ?_, ?_⟩
  · exact (tendsto_realizeL2Form_iff g μ
      (fun m => L2FormSpace.ofSection (As m) (hc m).2.2.2.1) (L2FormSpace.ofSection A hA)).mpr
      (by simpa only [L2FormSpace.toSection_ofSection] using htA)
  · exact (tendsto_realizeL2Form_iff g μ
      (fun m => L2FormSpace.ofSection (Ws m) (hc m).2.2.2.2.1) (L2FormSpace.ofSection W hW)).mpr
      (by simpa only [L2FormSpace.toSection_ofSection] using htW)

/-- Core pairs solve the actual forward finite chart equation, with their
true second entry as source and no deficiency shift. -/
theorem hodgeCorePair_chart_source {α : Type*} [Fintype α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : RealForm M k) (hc : OperatorCandidates.HodgeCorePair g.form μ A W)
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k)) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (r : α) :
    hodgeRegularityCoord b W x z r =
      -(∑ i, ∑ j, (realMetricFn g.form x z)⁻¹ i j *
        regularityDirection (realModelBasis n i)
          (regularityDirection (realModelBasis n j) (fun y => hodgeRegularityCoord b A x y r)) z) +
      (∑ c, ∑ i, hodgeRegularityE1 g.form x b r c i z *
        regularityDirection (realModelBasis n i) (fun y => hodgeRegularityCoord b A x y c) z) +
      ∑ c, hodgeRegularityE0 g.form x b r c z * hodgeRegularityCoord b A x z c := by
  have hW := (hodgeCorePair_iff_computed g μ hμ A W).mp hc
  rw [hW.2.2]
  exact hodgeRegularity_chart_system g μ hμ A hc.1 x b hz r

/-- The same core approximation is available at every degree for arbitrary
Hilbert graph entries, after internally constructing actual L² sections. -/
theorem hodgeClosureGraph_exists_actual_core
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (u w : L2FormHilbert g μ k) (hgraph : (u, w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph) :
    ∃ As Ws : ℕ → RealForm M k, ∃ hc : ∀ m, OperatorCandidates.HodgeCorePair g.form μ (As m) (Ws m),
      Tendsto (fun m => realizeActualForm g μ (As m) (hc m).2.2.2.1) atTop (𝓝 u) ∧
      Tendsto (fun m => realizeActualForm g μ (Ws m) (hc m).2.2.2.2.1) atTop (𝓝 w) := by
  obtain ⟨A, hA, hAr⟩ := l2FormHilbert_exists_section g μ u
  obtain ⟨W, hW, hWr⟩ := l2FormHilbert_exists_section g μ w
  have hg : (realizeActualForm g μ A hA, realizeActualForm g μ W hW) ∈
      (hodgeCoreOperator g μ hμ k).closure.graph := by
    simpa only [realizeActualForm, hAr, hWr] using hgraph
  simpa only [realizeActualForm, hAr, hWr] using
    hodgeClosureGraph_core_approximation g μ hμ A W hA hW hg

end Yau.NodeProofs.P06Aux
