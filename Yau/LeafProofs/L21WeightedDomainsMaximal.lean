import Yau.LeafProofs.L21WeightedDomainsRows

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ} {α β ι : Type*} [Fintype α] [Fintype ι]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem weightedRowsGraph_snd_eq_zero (K : ℝ) (hK : 0 ≤ K)
    (src : α → E →L[ℂ] WeightedScalar n K) (dst : β → F →L[ℂ] WeightedScalar n K)
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1))
    (hDst : ∀ y : F, (∀ r, dst r y = 0) → y = 0)
    (p : E × F) (hp : p ∈ weightedRowsGraph K hK src dst v a b ha hb) (hx : p.1 = 0) :
    p.2 = 0 := by
  apply hDst p.2
  intro r
  apply weightedCompactFunctional_separates K hK (dst r p.2)
  intro ψ
  have he := (weightedRowsGraph_mem_iff K hK src dst v a b ha hb p).mp hp r ψ
  simpa only [hx,map_zero,Finset.sum_const_zero] using he

/-- Maximal weak rows as an actual linear partial map. Its graph is
identified below using the concrete finite coordinate separation. -/
def weightedMaximalRows (K : ℝ) (hK : 0 ≤ K)
    (src : α → E →L[ℂ] WeightedScalar n K) (dst : β → F →L[ℂ] WeightedScalar n K)
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1)) : E →ₗ.[ℂ] F :=
  (weightedRowsGraph K hK src dst v a b ha hb).toLinearPMap

theorem weightedMaximalRows_graph (K : ℝ) (hK : 0 ≤ K)
    (src : α → E →L[ℂ] WeightedScalar n K) (dst : β → F →L[ℂ] WeightedScalar n K)
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1))
    (hDst : ∀ y : F, (∀ r, dst r y = 0) → y = 0) :
    (weightedMaximalRows K hK src dst v a b ha hb).graph =
      weightedRowsGraph K hK src dst v a b ha hb := by
  exact Submodule.toLinearPMap_graph_eq _ (weightedRowsGraph_snd_eq_zero K hK src dst v a b ha hb hDst)

theorem weightedMaximalRows_isClosed (K : ℝ) (hK : 0 ≤ K)
    (src : α → E →L[ℂ] WeightedScalar n K) (dst : β → F →L[ℂ] WeightedScalar n K)
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1))
    (hDst : ∀ y : F, (∀ r, dst r y = 0) → y = 0) :
    (weightedMaximalRows K hK src dst v a b ha hb).IsClosed := by
  change IsClosed ((weightedMaximalRows K hK src dst v a b ha hb).graph : Set (E × F))
  rw [weightedMaximalRows_graph K hK src dst v a b ha hb hDst]
  exact weightedRowsGraph_isClosed K hK src dst v a b ha hb

end Yau.LeafProofs.L21Aux
