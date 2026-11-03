import Yau.LeafProofs.L14JointPairRows
import Yau.LeafProofs.L14LocalFriedrichs

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
  (hE : Holomorphic (r := r) E)
  (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
  (hKO : K ⊆ localDomain (r := r) E a)

def localizedPairSystemInput (u : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ) (χ : ComplexVector n → ℝ)
    (z : ComplexVector n) (c : PairSystemInputIndex n r) : ℂ :=
  (χ z : ℂ)*compactPairHilbertField E g μ hμ h hh φ hφ a K hK hKO u w z c

def localizedPairSystemOutput (f : NQForm E 1)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ) (χ : ComplexVector n → ℝ)
    (z : ComplexVector n) (row : Fin n × Fin r) : ℂ :=
  localizedComplexSystemOutput realVec (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a) χ
    (compactPairHilbertField E g μ hμ h hh φ hφ a K hK hKO u w)
    (pairForcingDual E g h φ f a) z row

include hh hφ in
theorem localizedPairSystemInput_memLp
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ interior K) (c : PairSystemInputIndex n r) :
    MemLp (fun z => localizedPairSystemInput E g μ hμ h hh φ hφ a K hK hKO u w χ z c) 2 (lebesgueC n) :=
  localizedComplexSystemInput_memLp χ hχ hcχ hsχ _ fun L _ _ =>
    (compactPairHilbertField_memLp E g μ hμ h hh φ hφ a K hK hKO u w c).mono_measure Measure.restrict_le_self

include hh hφ in
theorem localizedPairSystemOutput_memLp
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ interior K) (row : Fin n × Fin r) :
    MemLp (fun z => localizedPairSystemOutput E g μ hμ h hh φ hφ a K hK hKO f u w χ z row) 2 (lebesgueC n) := by
  have hsub : interior K ⊆ localDomain (r := r) E a := interior_subset.trans hKO
  exact localizedComplexSystemOutput_memLp isOpen_interior realVec _
    (fun row c d => (alternatingPairFirstOrderDerivative_contDiffOn E g h hh φ hφ a row c d).mono hsub)
    χ hχ hcχ hsχ _ _
    (fun c L _ _ => (compactPairHilbertField_memLp E g μ hμ h hh φ hφ a K hK hKO u w c).mono_measure Measure.restrict_le_self)
    (fun row L hL hsL => chartOneDual_memLp_compact E g h hh φ hφ f hf a L hL (hsL.trans hsub) row.1 row.2) row

include hE in
theorem localized_joint_pair_complex_row
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hrep : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ t →
      inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
        inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) = weightedOneInner E g.form μ h φ f t.1.1)
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ interior K) (row : Fin n × Fin r)
    (ψ : ComplexVector n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∫ z,(ψ z : ℂ)*localizedPairSystemOutput E g μ hμ h hh φ hφ a K hK hKO f u w χ z row ∂lebesgueC n) =
      ∫ z,∑ c,localizedPairSystemInput E g μ hμ h hh φ hφ a K hK hKO u w χ z c *
        complexFormalAdjointTestRow realVec (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a)
          (alternatingPairFirstOrderValue (r := r) E g.form h φ a) row c ψ z ∂lebesgueC n := by
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume];infer_instance
  have hsub : interior K ⊆ localDomain (r := r) E a := interior_subset.trans hKO
  exact complex_firstOrder_rows_localize isOpen_interior realVec _ _
    (fun row c d => (alternatingPairFirstOrderDerivative_contDiffOn E g h hh φ hφ a row c d).mono hsub)
    (fun row c => (alternatingPairFirstOrderValue_contDiffOn E g h hh φ hφ a row c).mono hsub)
    (compactPairHilbertField E g μ hμ h hh φ hφ a K hK hKO u w) (pairForcingDual E g h φ f a)
    (fun c => ((compactPairHilbertField_memLp E g μ hμ h hh φ hφ a K hK hKO u w c).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
    (fun row => (chartOneDual_locallyIntegrableOn E g h hh φ hφ f hf a row.1 row.2).mono_set hsub)
    (fun row ψ hψ hcψ hsψ => compact_joint_pair_complex_row E g μ hμ h hh φ hφ hE a K hK hKO f hf u w hrep row ψ hψ hcψ (hsψ.trans interior_subset))
    χ hχ hcχ hsχ row ψ hψ hcψ

include hE in
theorem exists_localized_joint_pair_model_graph_approx
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ) (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hrep : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ t →
      inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
        inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) = weightedOneInner E g.form μ h φ f t.1.1)
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ interior K) :
    ∃ (L : Set (ComplexVector n)) (F : ℕ → ComplexVector n → PairSystemInputIndex n r → ℂ),
      IsCompact L ∧ L ⊆ interior K ∧
      (∀ m c,ContDiff ℝ ∞ (fun z => F m z c) ∧ tsupport (fun z => F m z c) ⊆ L) ∧
      (∀ c,(∀ m,MemLp (fun z => F m z c-localizedPairSystemInput E g μ hμ h hh φ hφ a K hK hKO u w χ z c) 2 (lebesgueC n)) ∧
        Tendsto (fun m => ∫ z,‖F m z c-localizedPairSystemInput E g μ hμ h hh φ hφ a K hK hKO u w χ z c‖^2 ∂lebesgueC n) atTop (𝓝 0)) ∧
      ∀ row,(∀ m,MemLp (fun z => complexFirstOrderSystemApply realVec
        (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a) (alternatingPairFirstOrderValue (r := r) E g.form h φ a) (F m) z row-
          localizedPairSystemOutput E g μ hμ h hh φ hφ a K hK hKO f u w χ z row) 2 (lebesgueC n)) ∧
        Tendsto (fun m => ∫ z,‖complexFirstOrderSystemApply realVec
          (alternatingPairFirstOrderDerivative (r := r) E g.form h φ a) (alternatingPairFirstOrderValue (r := r) E g.form h φ a) (F m) z row-
            localizedPairSystemOutput E g μ hμ h hh φ hφ a K hK hKO f u w χ z row‖^2 ∂lebesgueC n) atTop (𝓝 0) := by
  have hsub : interior K ⊆ localDomain (r := r) E a := interior_subset.trans hKO
  have hsInput (c : PairSystemInputIndex n r) :
      tsupport (fun z => localizedPairSystemInput E g μ hμ h hh φ hφ a K hK hKO u w χ z c) ⊆ tsupport χ :=
    tsupport_mul_subset_left.trans (tsupport_comp_subset (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero χ)
  exact exists_fixed_support_complex_firstOrder_graph_approx_norm isOpen_interior hcχ hsχ realVec _ _
    (fun row c d => (alternatingPairFirstOrderDerivative_contDiffOn E g h hh φ hφ a row c d).mono hsub)
    (fun row c => (alternatingPairFirstOrderValue_contDiffOn E g h hh φ hφ a row c).mono hsub)
    (localizedPairSystemInput E g μ hμ h hh φ hφ a K hK hKO u w χ)
    (localizedPairSystemOutput E g μ hμ h hh φ hφ a K hK hKO f u w χ)
    (localizedPairSystemInput_memLp E g μ hμ h hh φ hφ a K hK hKO u w χ hχ hcχ hsχ)
    (localizedPairSystemOutput_memLp E g μ hμ h hh φ hφ a K hK hKO f hf u w χ hχ hcχ hsχ)
    hsInput (localizedComplexSystemOutput_tsupport_subset realVec _ χ _ _)
    (localized_joint_pair_complex_row E g μ hμ h hh φ hφ hE a K hK hKO f hf u w hrep χ hχ hcχ hsχ)

end Yau.LeafProofs.L14Aux
