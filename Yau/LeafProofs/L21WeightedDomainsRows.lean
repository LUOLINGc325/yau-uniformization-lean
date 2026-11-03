import Yau.LeafProofs.L21WeightedDomainsCoordinates

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ} {α β ι : Type*} [Fintype α] [Fintype ι]

def weightedRowTranspose (v : ι → X n) (a : β → α → ι → X n → ℂ)
    (b : β → α → X n → ℂ) (r : β) (c : α)
    (ψ : X n → ℂ) (x : X n) : ℂ :=
  -(∑ i, (a r c i x*fderiv ℝ ψ x (v i)+fderiv ℝ (a r c i) x (v i)*ψ x))+b r c x*ψ x

theorem weightedRowTranspose_tsupport_subset
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (r : β) (c : α) (ψ : X n → ℂ) :
    tsupport (weightedRowTranspose v a b r c ψ) ⊆ tsupport ψ := by
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  have hd := fderiv_of_notMem_tsupport ℝ hn
  exact hx (by simp [weightedRowTranspose,hz,hd])

def weightedRowTransposeTest
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1))
    (r : β) (c : α) (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    CompactTest (Metric.ball (0 : X n) 1) := by
  have hf : ContDiffOn ℝ ∞ (weightedRowTranspose v a b r c ψ) (Metric.ball 0 1) := by
    have hdψ (i : ι) : ContDiff ℝ ∞ (fun x => fderiv ℝ ψ x (v i)) :=
      (ψ.property.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hda (i : ι) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (a r c i) x (v i)) (Metric.ball 0 1) :=
      ((ha r c i).fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const
    exact ((ContDiffOn.sum fun i _ => ((ha r c i).mul (hdψ i).contDiffOn).add
      ((hda i).mul ψ.property.1.contDiffOn)).neg).add ((hb r c).mul ψ.property.1.contDiffOn)
  have hs := weightedRowTranspose_tsupport_subset v a b r c (ψ : X n → ℂ)
  exact ⟨_,contDiff_of_contDiffOn_tsupport_subset Metric.isOpen_ball hf hs ψ.property.2.2,
    ψ.property.2.1.of_isClosed_subset (isClosed_tsupport _) hs,hs.trans ψ.property.2.2⟩

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def weightedRowsTestMap (K : ℝ) (hK : 0 ≤ K)
    (src : α → E →L[ℂ] WeightedScalar n K) (dst : β → F →L[ℂ] WeightedScalar n K)
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1))
    (r : β) (ψ : CompactTest (Metric.ball (0 : X n) 1)) : E × F →L[ℂ] ℂ :=
  (weightedCompactFunctional K hK ψ).comp ((dst r).comp (ContinuousLinearMap.snd ℂ E F))-
    ∑ c, (weightedCompactFunctional K hK (weightedRowTransposeTest v a b ha hb r c ψ)).comp
      ((src c).comp (ContinuousLinearMap.fst ℂ E F))

/-- The literal maximal distribution graph is an intersection of kernels
of actual continuous compact-test functionals. Unbounded zeroth-order
coefficients are permitted; only local smoothness is used. -/
def weightedRowsGraph (K : ℝ) (hK : 0 ≤ K)
    (src : α → E →L[ℂ] WeightedScalar n K) (dst : β → F →L[ℂ] WeightedScalar n K)
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1)) : Submodule ℂ (E × F) :=
  ⨅ r : β, ⨅ ψ : CompactTest (Metric.ball (0 : X n) 1),
    (weightedRowsTestMap K hK src dst v a b ha hb r ψ).ker

theorem weightedRowsGraph_mem_iff (K : ℝ) (hK : 0 ≤ K)
    (src : α → E →L[ℂ] WeightedScalar n K) (dst : β → F →L[ℂ] WeightedScalar n K)
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1)) (p : E × F) :
    p ∈ weightedRowsGraph K hK src dst v a b ha hb ↔
      ∀ r (ψ : CompactTest (Metric.ball (0 : X n) 1)),
        weightedCompactFunctional K hK ψ (dst r p.2) =
          ∑ c, weightedCompactFunctional K hK (weightedRowTransposeTest v a b ha hb r c ψ) (src c p.1) := by
  simp [weightedRowsGraph,weightedRowsTestMap,sub_eq_zero]

theorem weightedRowsGraph_isClosed (K : ℝ) (hK : 0 ≤ K)
    (src : α → E →L[ℂ] WeightedScalar n K) (dst : β → F →L[ℂ] WeightedScalar n K)
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1)) :
    IsClosed (weightedRowsGraph K hK src dst v a b ha hb : Set (E × F)) := by
  simp only [weightedRowsGraph,Submodule.coe_iInf]
  exact isClosed_iInter fun r => isClosed_iInter fun ψ =>
    (weightedRowsTestMap K hK src dst v a b ha hb r ψ).isClosed_ker

end Yau.LeafProofs.L21Aux
