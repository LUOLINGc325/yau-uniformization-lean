import Yau.LeafProofs.L03Complete
import Yau.LeafProofs.L03HodgeDivergenceWeak
import Yau.LeafProofs.L03CutoffEnergyBounds

/-! Source equations for the actual Hodge graph, in every degree and chart.
The output of the graph is retained as an arbitrary L² source. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology InnerProductSpace ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
open Yau.LeafProofs.L03.HodgeDivergenceWeak

variable {n k : ℕ} {M : ComplexManifold n}

/-- The closed graph gives the original distributional graph on any actual
representatives of its two Hilbert vectors. -/
theorem hodgeClosureGraph_maximal (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W : RealForm M k)
    (hA : L2RealForm g.form μ A) (hW : L2RealForm g.form μ W)
    (hgraph : (realizeActualForm g μ A hA, realizeActualForm g μ W hW) ∈
      (hodgeCoreOperator g μ hμ k).closure.graph) :
    OperatorCandidates.HodgeMaximalGraph g.form μ A W := by
  apply (hodgeMaximalGraph_iff_operator_adjoint g μ hμ A W hA hW).mpr
  rw [← hodgeCoreOperator_closure_eq_adjoint g μ hμ k]
  exact hgraph

/-- The actual Hodge graph implies a finite vector system with its genuine
volume-weighted Gram. Only the smooth compact test is differentiated. -/
theorem hodgeMaximalGraph_chart_vector_source
    {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : RealForm M k)
    (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A W)
    (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (G : ComplexVector n → Fiber n k) (hG : ContDiff ℝ ∞ G)
    (hcG : HasCompactSupport G) (hGO : tsupport G ⊆ chartTarget x) :
    (∫ z in chartTarget x, dotProduct (b.repr (chartForm A x z))
      ((gram g.form x b z).mulVec (b.repr (testOperator g.form x G z))) ∂lebesgueC n) =
    ∫ z in chartTarget x, dotProduct (b.repr (chartForm W x z))
      ((gram g.form x b z).mulVec (b.repr (G z))) ∂lebesgueC n := by
  let T := chartFormPushforward x G
  let Z := hodgeRealForm g.form k T
  have hT : SmoothRealForm T := chartFormPushforward_smooth x G hG hcG hGO
  have hcT : CompactlySupportedRealForm T := chartFormPushforward_compactlySupported x G hG hcG hGO
  have hTs := chartFormPushforward_source_support x G hG hcG hGO
  have hT0 (y : M.Carrier) (hy : y ∉ (extChartAt (ComplexModel n) x).source) : T y = 0 := by
    by_contra hn
    exact hy (hTs (subset_closure hn))
  have hZ0 (y : M.Carrier) (hy : y ∉ (extChartAt (ComplexModel n) x).source) : Z y = 0 := by
    by_contra hn
    exact hy (hTs ((hodgeRealForm_support_subset g μ hμ T hT) (subset_closure hn)))
  have heq := (hmax.2.2 T Z (hodgeRealForm_corePair g μ hμ T hT hcT)).2.2
  rw [integral_formInner_chart g μ hμ x A Z hmax.1
    (hodgeRealForm_l2 g μ hμ T hT hcT) hZ0,
    integral_formInner_chart g μ hμ x W T hmax.2.1
      (smooth_compactlySupported_l2RealForm g μ hμ T hT hcT) hT0] at heq
  calc
    _ = ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det *
        modelFormInner (realMetricFn g.form x z)⁻¹ (chartForm A x z) (chartForm Z x z)
          ∂lebesgueC n := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
      intro z hz
      dsimp only
      rw [← gram_pairing]
      congr 2
      exact (HodgeJets.chart_hodge_pushforward_expansion g μ hμ x G hG hcG hGO hz).symm
    _ = ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det *
        modelFormInner (realMetricFn g.form x z)⁻¹ (chartForm W x z) (chartForm T x z)
          ∂lebesgueC n := heq
    _ = _ := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
      intro z hz
      dsimp only
      rw [← gram_pairing, chartFormPushforward_to_chart x G hz]

/-- The same concrete source system follows directly from the original
closed operator graph. -/
theorem hodgeClosureGraph_chart_vector_source
    {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : RealForm M k) (hA : L2RealForm g.form μ A) (hW : L2RealForm g.form μ W)
    (hgraph : (realizeActualForm g μ A hA, realizeActualForm g μ W hW) ∈
      (hodgeCoreOperator g μ hμ k).closure.graph)
    (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (G : ComplexVector n → Fiber n k) (hG : ContDiff ℝ ∞ G)
    (hcG : HasCompactSupport G) (hGO : tsupport G ⊆ chartTarget x) :
    (∫ z in chartTarget x, dotProduct (b.repr (chartForm A x z))
      ((gram g.form x b z).mulVec (b.repr (testOperator g.form x G z))) ∂lebesgueC n) =
    ∫ z in chartTarget x, dotProduct (b.repr (chartForm W x z))
      ((gram g.form x b z).mulVec (b.repr (G z))) ∂lebesgueC n :=
  hodgeMaximalGraph_chart_vector_source g μ hμ A W
    (hodgeClosureGraph_maximal g μ hμ A W hA hW hgraph) x b G hG hcG hGO

/-- Smooth actual representatives are unique as dependent forms, including
all their values at individual points. -/
theorem smoothRealForm_eq_of_realize_eq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B)
    (hAL : L2RealForm g.form μ A) (hBL : L2RealForm g.form μ B)
    (heq : realizeActualForm g μ A hAL = realizeActualForm g μ B hBL) : A = B := by
  apply smoothRealForm_eq_of_ae g μ hμ A B hA hB
  exact (realizeL2Form_eq_iff_ae g μ (L2FormSpace.ofSection A hAL)
    (L2FormSpace.ofSection B hBL)).mp heq

end Yau.NodeProofs.P06Aux
