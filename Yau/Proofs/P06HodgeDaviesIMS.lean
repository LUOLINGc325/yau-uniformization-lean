import Yau.Proofs.P06HodgeDaviesMultipliers
import Yau.LeafProofs.L03HodgeIMS

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.Davies
open Yau Yau.LeafProofs Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- The actual compact Hodge core satisfies the relative weighted lower
bound. This is the exact IMS identity, with its nonnegative energy dropped. -/
theorem core_multiplier_lower (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (B : ℝ) (hB : 0 ≤ B)
    (hηb : ∀ x, |η x| ≤ B) (ell : ℝ)
    (hrel : ∀ x, L18Aux.scalarGradientPair g.form η η x ≤ ell ^ 2 * η x ^ 2)
    (A W : RealForm M k) (hc : OperatorCandidates.HodgeCorePair g.form μ A W) :
    let P := multiplyL2FormHilbert (k := k) g μ η
      (L18Aux.continuous_of_smoothFn hη).aestronglyMeasurable B hB hηb;
    let u := realizeL2Form g μ (L2FormSpace.ofSection A hc.2.2.2.1);
    let v := realizeL2Form g μ (L2FormSpace.ofSection W hc.2.2.2.2.1);
    -(ell ^ 2) * ‖P u‖ ^ 2 ≤ inner ℝ v (P (P u)) := by
  let hm := (L18Aux.continuous_of_smoothFn hη).aestronglyMeasurable (μ := μ)
  let P := multiplyL2FormHilbert (k := k) g μ η hm B hB hηb
  let u := realizeL2Form g μ (L2FormSpace.ofSection A hc.2.2.2.1)
  let v := realizeL2Form g μ (L2FormSpace.ofSection W hc.2.2.2.2.1)
  change -(ell ^ 2) * ‖P u‖ ^ 2 ≤ inner ℝ v (P (P u))
  obtain ⟨hA, hcA, hW⟩ := (hodgeCorePair_iff_computed g μ hμ A W).mp hc
  have hnorm : ‖P u‖ ^ 2 = ∫ x, formNormSq g.form (multiplyRealForm η A) x ∂μ := by
    dsimp only [P, u]
    rw [multiplyL2FormHilbert_realize, realizeL2Form_norm_sq]
    rfl
  have hpair : inner ℝ v (P (P u)) = ∫ x, formInner g.form
      (hodgeRealForm g.form k A) (multiplyRealForm (fun x => η x * η x) A) x ∂μ := by
    dsimp only [P, u, v]
    rw [multiplyL2FormHilbert_realize, multiplyL2FormHilbert_realize, realizeL2Form_inner]
    apply integral_congr_ae (Eventually.of_forall ?_)
    intro x
    simp only [multiplyL2FormLinear_toSection, L2FormSpace.toSection_ofSection, hW,
      multiplyRealForm_inner_right]
    ring
  have hi := integral_hodge_cutoff_IMS g μ hμ η hη A hA hcA
  have hpos : 0 ≤ ∫ x, hodgeEnergyDensity g.form k
      (multiplyRealForm η A) (multiplyRealForm η A) x ∂μ :=
    integral_nonneg (hodgeEnergyDensity_self_nonneg g.form _)
  have hgrad : (∫ x, L18Aux.scalarGradientPair g.form η η x *
      formNormSq g.form A x ∂μ) ≤
      ell ^ 2 * ∫ x, formNormSq g.form (multiplyRealForm η A) x ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun x => mul_nonneg
        (L18Aux.scalarGradientPair_self_nonneg g.form η x) (formNormSq_nonneg g.form A x))
      ((formNormSq_integrable g μ _
        (l2RealForm_multiply_bounded g μ η hm B hB hηb A hc.2.2.2.1)).const_mul _)
    apply Eventually.of_forall
    intro x
    change L18Aux.scalarGradientPair g.form η η x * formNormSq g.form A x ≤
      ell ^ 2 * formNormSq g.form (multiplyRealForm η A) x
    rw [multiplyRealForm_normSq]
    nlinarith [mul_le_mul_of_nonneg_right (hrel x) (formNormSq_nonneg g.form A x)]
  rw [← hnorm] at hgrad
  rw [← hpair] at hi
  linarith

/-- The weighted estimate extends to the original complete Hodge graph
because it contains only bounded multipliers and the two graph entries. -/
theorem graph_multiplier_lower (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (B : ℝ) (hB : 0 ≤ B)
    (hηb : ∀ x, |η x| ≤ B) (ell : ℝ)
    (hrel : ∀ x, L18Aux.scalarGradientPair g.form η η x ≤ ell ^ 2 * η x ^ 2)
    (u v : L2FormHilbert g μ k)
    (hgraph : (u, v) ∈ (hodgeCoreOperator g μ hμ k).closure.graph) :
    let P := multiplyL2FormHilbert (k := k) g μ η
      (L18Aux.continuous_of_smoothFn hη).aestronglyMeasurable B hB hηb;
    -(ell ^ 2) * ‖P u‖ ^ 2 ≤ inner ℝ v (P (P u)) := by
  let P := multiplyL2FormHilbert (k := k) g μ η
    (L18Aux.continuous_of_smoothFn hη).aestronglyMeasurable B hB hηb
  let T := hodgeCoreOperator g μ hμ k
  have hclosed : IsClosed {p : L2FormHilbert g μ k × L2FormHilbert g μ k |
      -(ell ^ 2) * ‖P p.1‖ ^ 2 ≤ inner ℝ p.2 (P (P p.1))} :=
    isClosed_le (continuous_const.mul ((continuous_norm.comp
      (P.continuous.comp continuous_fst)).pow 2))
      (continuous_snd.inner (P.continuous.comp (P.continuous.comp continuous_fst)))
  have hsub : (T.graph : Set (L2FormHilbert g μ k × L2FormHilbert g μ k)) ⊆
      {p | -(ell ^ 2) * ‖P p.1‖ ^ 2 ≤ inner ℝ p.2 (P (P p.1))} := by
    intro p hp
    have hp' : p ∈ hodgeCoreRealizedGraph g μ k := by
      change p ∈ (hodgeCoreOperator g μ hμ k).graph at hp
      rw [hodgeCoreOperator_graph] at hp
      change p ∈ hodgeCoreRealizedGraph g μ k at hp
      exact hp
    obtain ⟨A, W, hc, rfl⟩ := hp'
    exact core_multiplier_lower g μ hμ η hη B hB hηb ell hrel A W hc
  have hm : (u, v) ∈ closure (T.graph : Set (L2FormHilbert g μ k × L2FormHilbert g μ k)) := by
    rw [← T.graph.topologicalClosure_coe,
      (hodgeCoreOperator_closable g μ hμ k).graph_closure_eq_closure_graph]
    exact hgraph
  exact (closure_minimal hsub hclosed) hm

end Yau.NodeProofs.P06Aux.Davies
