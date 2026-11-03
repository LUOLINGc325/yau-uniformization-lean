import Yau.LeafProofs.L14TwoLocalCoefficient
import Yau.LeafProofs.L14TwoAdjointChart
import Yau.LeafProofs.L14TwoCoordinates

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
  (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
  (hKO : K ⊆ localDomain (r := r) E a) (ψ : ComplexVector n → ℂ)
  (hψ : MemLp ψ 2 ((lebesgueC n).restrict K)) (p : TwoCoefficientIndex n r)

def weightedTwoChartTest : WeightedTwoHilbert E g μ hμ h hh φ hφ →L[ℂ] ℂ :=
  (l2IntegralTest ((lebesgueC n).restrict K) ψ hψ).comp
    (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p)

theorem weightedTwoChartTest_realize_setIntegral (U : WeightedTwoSection E g μ hμ h hh φ hφ) :
    weightedTwoChartTest E g μ hμ h hh φ hφ a K hK hKO ψ hψ p
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ U) =
      ∫ z in K, coefficients (r := r) E U.1 a z ![p.1.2,p.2] p.1.1 * ψ z ∂lebesgueC n := by
  unfold weightedTwoChartTest
  rw [ContinuousLinearMap.comp_apply,weightedTwoHilbertLocalCoefficient_realize]
  exact l2IntegralTest_toLp _ ψ hψ _ (locallyL2_coefficients_memLp E U.1 U.2.1 a ![p.1.2,p.2] p.1.1 K hK hKO)

theorem weightedTwoChartTest_realize_integral (U : WeightedTwoSection E g μ hμ h hh φ hφ)
    (hsψ : Function.support ψ ⊆ K) :
    weightedTwoChartTest E g μ hμ h hh φ hφ a K hK hKO ψ hψ p
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ U) =
      ∫ z, coefficients (r := r) E U.1 a z ![p.1.2,p.2] p.1.1 * ψ z ∂lebesgueC n :=
  (weightedTwoChartTest_realize_setIntegral E g μ hμ h hh φ hφ a K hK hKO ψ hψ p U).trans
    (integral_mul_eq_setIntegral_of_support_subset (lebesgueC n) _ ψ K hsψ).symm

def weightedTwoChartStarTest (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) : ℂ :=
  star (weightedTwoChartTest E g μ hμ h hh φ hφ a K hK hKO (fun z => star (ψ z)) hψ.star p W)

theorem weightedTwoChartStarTest_continuous :
    Continuous (weightedTwoChartStarTest E g μ hμ h hh φ hφ a K hK hKO ψ hψ p) :=
  continuous_star.comp (weightedTwoChartTest E g μ hμ h hh φ hφ a K hK hKO (fun z => star (ψ z)) hψ.star p).continuous

theorem weightedTwoChartStarTest_realize_integral (U : WeightedTwoSection E g μ hμ h hh φ hφ)
    (hsψ : Function.support ψ ⊆ K) :
    weightedTwoChartStarTest E g μ hμ h hh φ hφ a K hK hKO ψ hψ p
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ U) =
      ∫ z, star (coefficients (r := r) E U.1 a z ![p.1.2,p.2] p.1.1) * ψ z ∂lebesgueC n := by
  have hsstar : Function.support (fun z => star (ψ z)) ⊆ K := by
    intro z hz
    apply hsψ
    intro he
    apply hz
    change star (ψ z) = 0
    rw [he,star_zero]
  have he := weightedTwoChartTest_realize_integral E g μ hμ h hh φ hφ a K hK hKO
    (fun z => star (ψ z)) (show MemLp (fun z => star (ψ z)) 2 ((lebesgueC n).restrict K) from hψ.star) p U hsstar
  change star (weightedTwoChartTest E g μ hμ h hh φ hφ a K hK hKO (fun z => star (ψ z)) hψ.star p
    (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)) = _
  calc
    _ = star (∫ z, coefficients (r := r) E U.1 a z ![p.1.2,p.2] p.1.1 * star (ψ z) ∂lebesgueC n) :=
      congrArg star he
    _ = _ := by
      rw [integral_star_complex]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        change star (coefficients (r := r) E U.1 a z ![p.1.2,p.2] p.1.1 * star (ψ z)) =
          star (coefficients (r := r) E U.1 a z ![p.1.2,p.2] p.1.1) * ψ z
        rw [star_mul,star_star,mul_comm]

include hh hφ in
theorem chartTwoDual_memLp_compact
    (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : tsupport F ⊆ localDomain (r := r) E a) (i j : Fin n) (α : Fin r) :
    MemLp (fun z => chartTwoDual E g.form h φ a F z i j α) 2 ((lebesgueC n).restrict K) :=
  compact_test_memLp _ (chartTwoDual_contDiff E g h hh φ hφ a F hF hsF i j α).continuous
    (hcF.of_isClosed_subset (isClosed_tsupport _) (tsupport_chartTwoDual_subset E g.form h φ a F i j α)) K

include hμ hh hφ in
theorem weightedTwoHilbert_chart_inner
    (hE : Holomorphic (r := r) E)
    (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hskew : ∀ z i j,F z j i = -F z i j) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : tsupport F ⊆ K)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    inner ℂ W (realizeWeightedTwoSection E g μ hμ h hh φ hφ
      (weightedTwoChartSection E g μ hμ h hh φ hφ hE a F hskew hF hcF (hsF.trans hKO))) =
      (2 : ℝ)^n • ((1/2 : ℂ)*∑ i,∑ j,∑ α,
        weightedTwoChartStarTest E g μ hμ h hh φ hφ a K hK hKO
          (fun z => chartTwoDual E g.form h φ a F z i j α)
          (chartTwoDual_memLp_compact E g h hh φ hφ a K F hF hcF (hsF.trans hKO) i j α) ((α,i),j) W) := by
  refine UniformSpace.Completion.induction_on W (isClosed_eq (by fun_prop) ?_) ?_
  · unfold weightedTwoChartStarTest
    fun_prop
  · intro U
    change inner ℂ (realizeWeightedTwoSection E g μ hμ h hh φ hφ U) _ = _
    rw [realizeWeightedTwoSection_inner]
    change (∫ x,weightedTwoPairing E g.form h φ U.1 (twoFormPushforward E a F) x ∂μ) = _
    rw [weightedTwoPairing_twoFormPushforward_integral E g μ hμ h hh φ hφ hE U.1 U.2.1 a F hF hcF (hsF.trans hKO) hskew]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro α _
    symm
    apply weightedTwoChartStarTest_realize_integral
    exact (subset_tsupport _).trans ((tsupport_chartTwoDual_subset E g.form h φ a F i j α).trans hsF)

theorem weightedTwoHilbertLocalCoefficient_skew
    (i j : Fin n) (α : Fin r) (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO ((α,j),i) W =
      -weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO ((α,i),j) W := by
  refine UniformSpace.Completion.induction_on W (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro U
  change weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO ((α,j),i)
    (realizeWeightedTwoSection E g μ hμ h hh φ hφ U) =
    -weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO ((α,i),j)
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)
  rw [weightedTwoHilbertLocalCoefficient_realize E g μ hμ h hh φ hφ a K hK hKO ((α,j),i),
    weightedTwoHilbertLocalCoefficient_realize E g μ hμ h hh φ hφ a K hK hKO ((α,i),j)]
  apply Lp.ext
  filter_upwards [weightedTwoLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hKO ((α,j),i) U,
    weightedTwoLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hKO ((α,i),j) U,
    Lp.coeFn_neg (weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO ((α,i),j) U)] with z hji hij hneg
  rw [hji,hneg,Pi.neg_apply,hij]
  exact coefficients_two_skew E U.1 a z i j α

theorem weightedTwoHilbertLocalCoefficient_skew_ae
    (i j : Fin n) (α : Fin r) (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    (fun z => weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO ((α,j),i) W z) =ᵐ[
      (lebesgueC n).restrict K]
      (fun z => -weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO ((α,i),j) W z) := by
  rw [weightedTwoHilbertLocalCoefficient_skew E g μ hμ h hh φ hφ a K hK hKO i j α W]
  exact Lp.coeFn_neg _

end Yau.LeafProofs.L14Aux
