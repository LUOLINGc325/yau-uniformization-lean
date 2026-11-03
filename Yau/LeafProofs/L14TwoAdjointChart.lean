import Yau.LeafProofs.L14TwoAdjointGreen
import Yau.LeafProofs.L14TwoPairingChart

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

include hE in
theorem weakDbar_weighted_chartTwo_adjoint_pairing
    (U : WeightedOneSection E g μ hμ h hh φ hφ) (f : NQForm E 2)
    (huf : WeakDbar (r := r) E U.1 f)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F) (hsF : tsupport F ⊆ localDomain (r := r) E a)
    (hskew : ∀ z i j, F z j i = -F z i j) :
    (∫ x, weightedTwoPairing E g.form h φ f (twoFormPushforward (r := r) E a F) x ∂μ) =
      weightedOneInner E g.form μ h φ U.1
        (oneFormPushforward (r := r) E a (chartTwoDbarAdjoint E g.form h φ a F)) := by
  classical
  let R := chartTwoDbarAdjoint E g.form h φ a F
  have hR : ContDiff ℝ ∞ R := chartTwoDbarAdjoint_contDiff E g h hh φ hφ a F hF hsF
  have hsR : tsupport R ⊆ tsupport F := tsupport_chartTwoDbarAdjoint_subset E g.form h φ a F
  have hcR : HasCompactSupport R := hcF.of_isClosed_subset (isClosed_tsupport _) hsR
  have hi (j : Fin n) (α : Fin r) : Integrable
      (fun z => star (coefficients (r := r) E U.1 a z (fun _ => j) α) * chartOneDual (r := r) E g.form h φ a R z j α)
      (lebesgueC n) := by
    have hs := tsupport_chartOneDual_subset E g.form h φ a R j α
    exact locallyL2_star_test_integrable E U.1 U.2.1 a (fun _ => j) α _
      (chartOneDual_contDiff E g h hh φ hφ a R hR (hsR.trans hsF) j α).continuous
      (hcR.of_isClosed_subset (isClosed_tsupport _) hs) (hs.trans (hsR.trans hsF))
  have hIntegral : (∫ z, ∑ j, ∑ α,
      star (coefficients (r := r) E U.1 a z (fun _ => j) α) * chartOneDual (r := r) E g.form h φ a R z j α ∂lebesgueC n) =
      ∑ j, ∑ α, ∫ z, star (coefficients (r := r) E U.1 a z (fun _ => j) α) *
        chartOneDual (r := r) E g.form h φ a R z j α ∂lebesgueC n := by
    rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ (fun α _ => hi j α))]
    exact Finset.sum_congr rfl fun j _ => integral_finsetSum Finset.univ (fun α _ => hi j α)
  rw [weightedTwoPairing_twoFormPushforward_integral E g μ hμ h hh φ hφ hE f huf.2.1 a F hF hcF hsF hskew,
    weakDbar_chartTwo_adjoint_pairing E g h hh φ hφ U.1 f huf a F hF hcF hsF hskew,
    weightedOneInner_oneFormPushforward_right E g μ hμ h hh φ hφ hE a R hR hcR (hsR.trans hsF) U,
    hIntegral]

include hμ hh hφ hE in
def weightedTwoChartSection (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hskew : ∀ z i j, F z j i = -F z i j) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : tsupport F ⊆ localDomain (r := r) E a) : WeightedTwoSection E g μ hμ h hh φ hφ :=
  ⟨twoFormPushforward (r := r) E a F, twoFormPushforward_weightedL2 E g μ hμ h hh φ hφ hE a F hskew hF hcF hsF⟩

include hμ hh hφ hE in
def weightedTwoDbarAdjointChartSection (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F) (hsF : tsupport F ⊆ localDomain (r := r) E a) :
    WeightedOneSection E g μ hμ h hh φ hφ :=
  weightedOneChartSection E g μ hμ h hh φ hφ hE a (chartTwoDbarAdjoint E g.form h φ a F)
    (chartTwoDbarAdjoint_contDiff E g h hh φ hφ a F hF hsF)
    (hcF.of_isClosed_subset (isClosed_tsupport _) (tsupport_chartTwoDbarAdjoint_subset E g.form h φ a F))
    ((tsupport_chartTwoDbarAdjoint_subset E g.form h φ a F).trans hsF)

include hE in
theorem weightedTwo_adjoint_chart_inner
    (U : WeightedOneSection E g μ hμ h hh φ hφ) (D : WeightedTwoSection E g μ hμ h hh φ hφ)
    (hUD : WeakDbar (r := r) E U.1 D.1)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hskew : ∀ z i j, F z j i = -F z i j) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : tsupport F ⊆ localDomain (r := r) E a) :
    inner ℂ (realizeWeightedTwoSection E g μ hμ h hh φ hφ D)
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ
        (weightedTwoChartSection E g μ hμ h hh φ hφ hE a F hskew hF hcF hsF)) =
      inner ℂ (realizeWeightedOneSection E g μ hμ h hh φ hφ U)
        (realizeWeightedOneSection E g μ hμ h hh φ hφ
          (weightedTwoDbarAdjointChartSection E g μ hμ h hh φ hφ hE a F hF hcF hsF)) := by
  rw [realizeWeightedTwoSection_inner, realizeWeightedOneSection_inner]
  exact weakDbar_weighted_chartTwo_adjoint_pairing E g μ hμ h hh φ hφ hE U D.1 hUD a F hF hcF hsF hskew

end Yau.LeafProofs.L14Aux
