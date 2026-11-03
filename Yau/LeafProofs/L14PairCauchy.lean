import Yau.LeafProofs.L14CompactTwoAdjoint
import Yau.LeafProofs.L14CutoffNorm

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar

theorem cauchySeq_pair_of_norm_sub_sq {H : Type*} [NormedAddCommGroup H]
    (A B : ℕ → H)
    (heq : ∀ j k,‖(A j+B j)-(A k+B k)‖^2 = ‖A j-A k‖^2+‖B j-B k‖^2)
    (hsum : CauchySeq (fun j => A j+B j)) : CauchySeq A ∧ CauchySeq B := by
  have hA (j k : ℕ) : dist (A j) (A k) ≤ dist (A j+B j) (A k+B k) := by
    rw [dist_eq_norm,dist_eq_norm]
    have h := heq j k
    nlinarith [norm_nonneg (A j-A k),norm_nonneg ((A j+B j)-(A k+B k)),sq_nonneg ‖B j-B k‖]
  have hB (j k : ℕ) : dist (B j) (B k) ≤ dist (A j+B j) (A k+B k) := by
    rw [dist_eq_norm,dist_eq_norm]
    have h := heq j k
    nlinarith [norm_nonneg (B j-B k),norm_nonneg ((A j+B j)-(A k+B k)),sq_nonneg ‖A j-A k‖]
  constructor
  · apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hsum ε hε
    exact ⟨N,fun j hj k hk => (hA j k).trans_lt (hN j hj k hk)⟩
  · apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hsum ε hε
    exact ⟨N,fun j hj k hk => (hB j k).trans_lt (hN j hj k hk)⟩

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

theorem co_closed_realize_sub
    (R S : WeightedOneSection E g μ hμ h hh φ hφ)
    (hR : (realizeWeightedOneSection E g μ hμ h hh φ hφ R,(0 : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (hS : (realizeWeightedOneSection E g μ hμ h hh φ hφ S,(0 : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph) :
    (realizeWeightedOneSection E g μ hμ h hh φ hφ (R-S),(0 : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph := by
  rw [realizeWeightedOneSection_sub]
  have he := Submodule.sub_mem (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph hR hS
  simpa only [Prod.mk_sub_mk,sub_self] using he

include hE in
theorem dbar_twoAdjoint_norm_sub_sq
    (R S : WeightedOneSection E g μ hμ h hh φ hφ)
    (hR : (realizeWeightedOneSection E g μ hμ h hh φ hφ R,(0 : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (hS : (realizeWeightedOneSection E g μ hμ h hh φ hφ S,(0 : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (u v : (weightedMaximalDbar E g μ hμ h hh φ hφ).domain) :
    ‖(weightedMaximalDbar E g μ hμ h hh φ hφ u+realizeWeightedOneSection E g μ hμ h hh φ hφ R)-
      (weightedMaximalDbar E g μ hμ h hh φ hφ v+realizeWeightedOneSection E g μ hμ h hh φ hφ S)‖^2 =
      ‖weightedMaximalDbar E g μ hμ h hh φ hφ u-weightedMaximalDbar E g μ hμ h hh φ hφ v‖^2+
        ‖realizeWeightedOneSection E g μ hμ h hh φ hφ R-realizeWeightedOneSection E g μ hμ h hh φ hφ S‖^2 := by
  have he := dbar_twoAdjoint_norm_add_sq E g μ hμ h hh φ hφ hE (R-S)
    (co_closed_realize_sub E g μ hμ h hh φ hφ R S hR hS) (u-v)
  rw [LinearPMap.map_sub,realizeWeightedOneSection_sub] at he
  convert he using 1 <;> congr 1 <;> abel

include hE in
theorem dbar_twoAdjoint_cauchySeq_of_sum
    (R : ℕ → WeightedOneSection E g μ hμ h hh φ hφ)
    (hR : ∀ j,(realizeWeightedOneSection E g μ hμ h hh φ hφ (R j),(0 : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (u : ℕ → (weightedMaximalDbar E g μ hμ h hh φ hφ).domain)
    (hsum : CauchySeq (fun j => weightedMaximalDbar E g μ hμ h hh φ hφ (u j)+
      realizeWeightedOneSection E g μ hμ h hh φ hφ (R j))) :
    CauchySeq (fun j => weightedMaximalDbar E g μ hμ h hh φ hφ (u j)) ∧
      CauchySeq (fun j => realizeWeightedOneSection E g μ hμ h hh φ hφ (R j)) :=
  cauchySeq_pair_of_norm_sub_sq _ _
    (fun j k => dbar_twoAdjoint_norm_sub_sq E g μ hμ h hh φ hφ hE (R j) (R k) (hR j) (hR k) (u j) (u k)) hsum

end Yau.LeafProofs.L14Aux
