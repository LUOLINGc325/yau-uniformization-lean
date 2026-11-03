import Yau.LeafProofs.L14CompactRieszPair
import Yau.LeafProofs.L14TwoHilbertTest
import Yau.LeafProofs.L14RoughOnePairing

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

/-- The chart test and its two actual graph outputs. -/
def compactChartJointTriple (a : M.Carrier)
    (G : ComplexVector n → Fin n → ComplexVector r)
    (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G)
    (hsG : tsupport G ⊆ localDomain (r := r) E a) :
    CompactJointTriple E g μ hμ h hh φ hφ :=
  (weightedOneChartSection E g μ hμ h hh φ hφ hE a G hG hcG hsG,
    weightedDbarAdjointChartSection E g μ hμ h hh φ hφ hE a G hG hcG hsG,
    weightedTwoChartSection E g μ hμ h hh φ hφ hE a (modelOneDbar G)
      (modelOneDbar_skew G) (modelOneDbar_contDiff G hG)
      (hcG.of_isClosed_subset (isClosed_tsupport _) (tsupport_modelOneDbar_subset G))
      ((tsupport_modelOneDbar_subset G).trans hsG))

theorem compactChartJointTriple_isCompact (a : M.Carrier)
    (G : ComplexVector n → Fin n → ComplexVector r)
    (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G)
    (hsG : tsupport G ⊆ localDomain (r := r) E a) :
    IsCompactJointTriple E g μ hμ h hh φ hφ
      (compactChartJointTriple E g μ hμ h hh φ hφ hE a G hG hcG hsG) := by
  have hS := weightedDbarAdjointChartSection_smooth_compact E g μ hμ h hh φ hφ hE a G hG hcG hsG
  have hK : IsCompact (chartInv a '' tsupport G) := hcG.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hsG.trans Set.inter_subset_left))
  refine ⟨oneFormPushforward_smooth E hE a G hG hcG hsG,
    hK.of_isClosed_subset isClosed_closure (oneFormPushforward_support E a G hcG hsG),
    hS.1,hS.2,twoFormPushforward_modelOneDbar_smooth E hE a G hG hcG hsG,
    twoFormPushforward_compact E a (modelOneDbar G)
      (hcG.of_isClosed_subset (isClosed_tsupport _) (tsupport_modelOneDbar_subset G))
      ((tsupport_modelOneDbar_subset G).trans hsG),
    oneFormPushforward_representsDbar E hE a G hG hcG hsG,
    weightedMaximalDbar_adjoint_chart E g μ hμ h hh φ hφ hE a G hG hcG hsG⟩

variable (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
  (hKO : K ⊆ localDomain (r := r) E a)

/-- The conjugate test is the set integral of the actual local L2 representative. -/
theorem weightedTwoChartStarTest_apply_setIntegral
    (ψ : ComplexVector n → ℂ) (hψ : MemLp ψ 2 ((lebesgueC n).restrict K))
    (p : TwoCoefficientIndex n r) (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    weightedTwoChartStarTest E g μ hμ h hh φ hφ a K hK hKO ψ hψ p W =
      ∫ z in K, star (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p W z) *
        ψ z ∂lebesgueC n := by
  let L := weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p W
  have he : l2IntegralTest ((lebesgueC n).restrict K) (fun z => star (ψ z)) hψ.star L =
      ∫ z in K, L z * star (ψ z) ∂lebesgueC n := by
    have ht := l2IntegralTest_toLp ((lebesgueC n).restrict K)
      (fun z => star (ψ z)) hψ.star L (Lp.memLp L)
    rw [Lp.toLp_coeFn] at ht
    exact ht
  change star (l2IntegralTest ((lebesgueC n).restrict K) (fun z => star (ψ z)) hψ.star L) = _
  rw [he,integral_star_complex]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    change star (L z * star (ψ z)) = star (L z) * ψ z
    rw [star_mul,star_star,mul_comm]

theorem weightedTwoHilbertLocalCoefficient_star_mul_integrable
    (ψ : ComplexVector n → ℂ) (hψ : MemLp ψ 2 ((lebesgueC n).restrict K))
    (p : TwoCoefficientIndex n r) (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    Integrable (fun z =>
      star (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p W z) * ψ z)
      ((lebesgueC n).restrict K) :=
  test_mul_integrable_of_memLp _ _ ψ
    (Lp.memLp (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p W)).star hψ

/-- Every top-degree coefficient test in the model identity is integrable. -/
theorem compact_riesz_chart_top_coefficient_integrable
    (U : WeightedTopSection E g μ hμ h hh φ hφ)
    (G : ComplexVector n → Fin n → ComplexVector r)
    (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G)
    (hsG : tsupport G ⊆ localDomain (r := r) E a) (α : Fin r) :
    Integrable (fun z => star (coefficients (r := r) E U.1 a z Fin.elim0 α) *
      ((∑ β, BundleDbar.metricMatrix (r := r) E h a z α β *
        chartDbarAdjoint E g.form h φ a G z β) *
        (Real.exp (-φ (chartInv a z)) : ℂ))) (lebesgueC n) := by
  classical
  let ψ := fun z => (∑ β, BundleDbar.metricMatrix (r := r) E h a z α β *
    chartDbarAdjoint E g.form h φ a G z β) * (Real.exp (-φ (chartInv a z)) : ℂ)
  have hsψ : tsupport ψ ⊆ tsupport G := by
    apply closure_minimal _ (isClosed_tsupport G)
    intro z hz
    by_contra hn
    apply hz
    have hδ : chartDbarAdjoint E g.form h φ a G z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun ht => hn (tsupport_chartDbarAdjoint_subset E g.form h φ a G ht))
    simp [ψ,hδ]
  have hψ : ContDiff ℝ ∞ ψ := by
    apply contDiff_of_contDiffOn_of_tsupport_subset (localDomain_isOpen E a) _ _ (hsψ.trans hsG)
    have hδ := chartDbarAdjoint_contDiff E g h hh φ hφ a G hG hsG
    have hρ : ContDiffOn ℝ ∞ (fun z => (Real.exp (-φ (chartInv a z)) : ℂ))
        (localDomain (r := r) E a) :=
      (((hφ a).neg.exp).continuousLinearMap_comp Complex.ofRealCLM).mono Set.inter_subset_left
    apply ContDiffOn.mul _ hρ
    apply ContDiffOn.sum
    intro β _
    exact (hh a α β).mul (((contDiff_piLp 2).mp hδ β).contDiffOn)
  exact locallyL2_conjugate_test_integrable E U.1 U.2.1 a Fin.elim0 α ψ hψ.continuous
    (hcG.of_isClosed_subset (isClosed_tsupport _) hsψ) (hsψ.trans hsG)

/-- All integrals in the chart identity are finite, using only local L2 for the source. -/
theorem compact_riesz_chart_integrable
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (G : ComplexVector n → Fin n → ComplexVector r)
    (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G) (hsG : tsupport G ⊆ K) :
    Integrable (fun z => ∑ i, ∑ α, star (coefficients (r := r) E f a z (fun _ => i) α) *
      chartOneDual E g.form h φ a G z i α) (lebesgueC n) ∧
    Integrable (fun z => ∑ α,
      star (coefficients (r := r) E (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u).1 a z Fin.elim0 α) *
        ((∑ β, BundleDbar.metricMatrix (r := r) E h a z α β * chartDbarAdjoint E g.form h φ a G z β) *
          (Real.exp (-φ (chartInv a z)) : ℂ))) (lebesgueC n) ∧
    ∀ i j α, Integrable (fun z =>
      star (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO ((α,i),j) w z) *
        chartTwoDual E g.form h φ a (modelOneDbar G) z i j α) ((lebesgueC n).restrict K) := by
  classical
  have hsGO := hsG.trans hKO
  have hcD := hcG.of_isClosed_subset (isClosed_tsupport _) (tsupport_modelOneDbar_subset G)
  have hsDO := (tsupport_modelOneDbar_subset G).trans hsGO
  refine ⟨integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun α _ =>
    chartOneDual_conjugate_test_integrable E g h hh φ hφ f hf a G hG hcG hsGO i α)),
    integrable_finsetSum _ (fun α _ => compact_riesz_chart_top_coefficient_integrable
      E g μ hμ h hh φ hφ a (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u) G hG hcG hsGO α), ?_⟩
  intro i j α
  exact weightedTwoHilbertLocalCoefficient_star_mul_integrable E g μ hμ h hh φ hφ a K hK hKO
    _ (chartTwoDual_memLp_compact E g h hh φ hφ a K (modelOneDbar G)
      (modelOneDbar_contDiff G hG) hcD hsDO i j α) ((α,i),j) w

include hE in
/-- The compact joint graph identity in a fixed chart, with the common density factor cancelled. -/
theorem compact_joint_riesz_pair_chart_identity
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f)
    (u : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (w : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (hrep : ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
      IsCompactJointTriple E g μ hμ h hh φ hφ t →
      inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
        inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) =
          weightedOneInner E g.form μ h φ f t.1.1)
    (G : ComplexVector n → Fin n → ComplexVector r)
    (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G) (hsG : tsupport G ⊆ K) :
    (∫ z, ∑ i, ∑ α, star (coefficients (r := r) E f a z (fun _ => i) α) *
      chartOneDual E g.form h φ a G z i α ∂lebesgueC n) =
    (∫ z, ∑ α,
      star (coefficients (r := r) E (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u).1 a z Fin.elim0 α) *
        ((∑ β, BundleDbar.metricMatrix (r := r) E h a z α β * chartDbarAdjoint E g.form h φ a G z β) *
          (Real.exp (-φ (chartInv a z)) : ℂ)) ∂lebesgueC n) +
      (1/2 : ℂ) * ∑ i, ∑ j, ∑ α, ∫ z in K,
        star (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO ((α,i),j) w z) *
          chartTwoDual E g.form h φ a (modelOneDbar G) z i j α ∂lebesgueC n := by
  classical
  have hsGO := hsG.trans hKO
  have hcD := hcG.of_isClosed_subset (isClosed_tsupport _) (tsupport_modelOneDbar_subset G)
  have hsDK := (tsupport_modelOneDbar_subset G).trans hsG
  have hsDO := hsDK.trans hKO
  let U := weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u
  let δ := chartDbarAdjoint E g.form h φ a G
  have hδ := chartDbarAdjoint_contDiff E g h hh φ hφ a G hG hsGO
  have hcδ := hcG.of_isClosed_subset (isClosed_tsupport _) (tsupport_chartDbarAdjoint_subset E g.form h φ a G)
  have hsδ := (tsupport_chartDbarAdjoint_subset E g.form h φ a G).trans hsGO
  have he := hrep (compactChartJointTriple E g μ hμ h hh φ hφ hE a G hG hcG hsGO)
    (compactChartJointTriple_isCompact E g μ hμ h hh φ hφ hE a G hG hcG hsGO)
  have htop : inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ
      (weightedDbarAdjointChartSection E g μ hμ h hh φ hφ hE a G hG hcG hsGO)) =
      (2 : ℝ)^n • (∫ z, ∑ α, star (coefficients (r := r) E U.1 a z Fin.elim0 α) *
        ((∑ β, BundleDbar.metricMatrix (r := r) E h a z α β * δ z β) *
          (Real.exp (-φ (chartInv a z)) : ℂ)) ∂lebesgueC n) := by
    rw [← weightedTopHilbertRepresentative_realize E g μ hμ h hh φ hφ u,realizeWeightedTopSection_inner]
    change weightedTopInner E g.form μ h φ U.1 (topFormPushforward E a δ) = _
    rw [weightedTopInner_topFormPushforward_right E g μ hμ h hh φ hφ hE a δ hδ hcδ hsδ U]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
  have htwo := weightedTwoHilbert_chart_inner E g μ hμ h hh φ hφ a K hK hKO hE
    (modelOneDbar G) (modelOneDbar_skew G) (modelOneDbar_contDiff G hG) hcD hsDK w
  simp_rw [weightedTwoChartStarTest_apply_setIntegral] at htwo
  change inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ
      (weightedDbarAdjointChartSection E g μ hμ h hh φ hφ hE a G hG hcG hsGO)) +
    inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ
      (weightedTwoChartSection E g μ hμ h hh φ hφ hE a (modelOneDbar G)
        (modelOneDbar_skew G) (modelOneDbar_contDiff G hG) hcD hsDO)) =
    weightedOneInner E g.form μ h φ f (oneFormPushforward E a G) at he
  rw [htop,htwo,locallyL2_weightedOneInner_oneFormPushforward E g μ hμ h hh φ hφ hE f hf a G hG hcG hsGO] at he
  apply smul_right_injective ℂ (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0))
  simpa only [smul_add] using he.symm

end Yau.LeafProofs.L14Aux
