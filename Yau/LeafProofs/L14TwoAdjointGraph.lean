import Yau.LeafProofs.L14CompactTwoAdjoint

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

def weightedTwoAdjointGraph : Submodule ℂ
    (WeightedTwoHilbert E g μ hμ h hh φ hφ × WeightedOneHilbert E g μ hμ h hh φ hφ) where
  carrier := {p | ∀ (U : WeightedOneSection E g μ hμ h hh φ hφ) (D : WeightedTwoSection E g μ hμ h hh φ hφ),
    WeakDbar (r := r) E U.1 D.1 →
      inner ℂ (realizeWeightedTwoSection E g μ hμ h hh φ hφ D) p.1 =
        inner ℂ (realizeWeightedOneSection E g μ hμ h hh φ hφ U) p.2}
  zero_mem' := by intro U D hUD;simp
  add_mem' := by
    intro p q hp hq U D hUD
    simp only [Prod.fst_add,Prod.snd_add,inner_add_right]
    rw [hp U D hUD,hq U D hUD]
  smul_mem' := by
    intro c p hp U D hUD
    change inner ℂ (realizeWeightedTwoSection E g μ hμ h hh φ hφ D) (c • p.1) =
      inner ℂ (realizeWeightedOneSection E g μ hμ h hh φ hφ U) (c • p.2)
    rw [inner_smul_right,inner_smul_right,hp U D hUD]

theorem weightedTwoAdjointGraph_isClosed :
    IsClosed (weightedTwoAdjointGraph E g μ hμ h hh φ hφ :
      Set (WeightedTwoHilbert E g μ hμ h hh φ hφ × WeightedOneHilbert E g μ hμ h hh φ hφ)) := by
  change IsClosed {p : WeightedTwoHilbert E g μ hμ h hh φ hφ × WeightedOneHilbert E g μ hμ h hh φ hφ | ∀ (U : WeightedOneSection E g μ hμ h hh φ hφ) (D : WeightedTwoSection E g μ hμ h hh φ hφ),
    WeakDbar (r := r) E U.1 D.1 →
      inner ℂ (realizeWeightedTwoSection E g μ hμ h hh φ hφ D) p.1 =
        inner ℂ (realizeWeightedOneSection E g μ hμ h hh φ hφ U) p.2}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun U => isClosed_iInter fun D => isClosed_iInter fun _ =>
    isClosed_eq (by fun_prop) (by fun_prop)

theorem weightedTwoAdjointGraph_closed_limit
    (W : ℕ → WeightedTwoHilbert E g μ hμ h hh φ hφ) (R : ℕ → WeightedOneHilbert E g μ hμ h hh φ hφ)
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ) (b : WeightedOneHilbert E g μ hμ h hh φ hφ)
    (hmem : ∀ j,(W j,R j) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ)
    (hW : Tendsto W atTop (𝓝 w)) (hR : Tendsto R atTop (𝓝 b)) :
    (w,b) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ :=
  (weightedTwoAdjointGraph_isClosed E g μ hμ h hh φ hφ).mem_of_tendsto (hW.prodMk_nhds hR) (Eventually.of_forall hmem)

variable (hE : Holomorphic (r := r) E)

include hE in
theorem weightedTwoAdjointGraph_chart
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hskew : ∀ z i j,F z j i = -F z i j) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : tsupport F ⊆ localDomain (r := r) E a) :
    (realizeWeightedTwoSection E g μ hμ h hh φ hφ (weightedTwoChartSection E g μ hμ h hh φ hφ hE a F hskew hF hcF hsF),
      realizeWeightedOneSection E g μ hμ h hh φ hφ (weightedTwoDbarAdjointChartSection E g μ hμ h hh φ hφ hE a F hF hcF hsF)) ∈
      weightedTwoAdjointGraph E g μ hμ h hh φ hφ := by
  intro U D hUD
  exact weightedTwo_adjoint_chart_inner E g μ hμ h hh φ hφ hE U D hUD a F hskew hF hcF hsF

include hE in
theorem weightedTwoAdjointGraph_co_closed
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ) (b : WeightedOneHilbert E g μ hμ h hh φ hφ)
    (hwb : (w,b) ∈ weightedTwoAdjointGraph E g μ hμ h hh φ hφ) :
    (b,(0 : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph := by
  let T := weightedMaximalDbar E g μ hμ h hh φ hφ
  have hp (x : T.domain) : inner ℂ (0 : WeightedTopHilbert E g μ hμ h hh φ hφ)
      (x : WeightedTopHilbert E g μ hμ h hh φ hφ) = inner ℂ b (T x) := by
    let D := weightedOneHilbertRepresentative E g μ hμ h hh φ hφ (T x)
    have hclosed : WeaklyClosed (r := r) E D.1 := weightedMaximalDbar_apply_weaklyClosed E g μ hμ h hh φ hφ x
    have he := hwb D 0 (weakDbar_zero_of_weaklyClosed E D.1 hclosed)
    rw [weightedOneHilbertRepresentative_realize] at he
    have hz : inner ℂ (T x) b = 0 := by simpa only [realizeWeightedTwoSection,UniformSpace.Completion.coe_zero,inner_zero_left] using he.symm
    rw [inner_zero_left]
    symm
    rw [← inner_conj_symm b (T x),hz,map_zero]
  have hb : b ∈ T.adjoint.domain := LinearPMap.mem_adjoint_domain_of_exists b ⟨0,hp⟩
  have hout : T.adjoint ⟨b,hb⟩ = 0 :=
    LinearPMap.adjoint_apply_eq (weightedMaximalDbar_domain_dense E g μ hμ h hh φ hφ hE) _ hp
  exact T.adjoint.mem_graph_iff.mpr ⟨⟨b,hb⟩,rfl,hout⟩

end Yau.LeafProofs.L14Aux
