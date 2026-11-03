import Yau.LeafProofs.L14InverseMeasurable
import Yau.LeafProofs.L14RoughOnePairing
import Yau.LeafProofs.L14CompactBKN

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

theorem weightedSourcePairing_eq_weightedOnePairing
    (f V : NQForm E 1) :
    weightedSourcePairing (r := r) E g.form h φ f
      (fun x i α => coefficients (r := r) E V x (chartPt x x) (fun _ => i) α) =
      weightedOnePairing E g.form h φ f V := by
  funext x
  unfold weightedSourcePairing sourceCoefficientPairing weightedOnePairing
  rw [oneFormPairing_eq_coefficientInner (r := r)]

include hμ hh hφ hE in
theorem compact_source_curvature_bound
    (hN : WeightedNakanoNonnegative (r := r) E h φ)
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f)
    (hfinite : inverseCurvatureIntegral (r := r) E g.form h μ φ f < ⊤)
    (V : NQForm E 1) (hV : SmoothForm (r := r) E V)
    (hcV : IsCompact (closure {x | V x ≠ (0 : NQForm E 1) x})) :
    ‖weightedOneInner E g.form μ h φ f V‖ ^ 2 ≤
      (inverseCurvatureIntegral (r := r) E g.form h μ φ f).toReal *
        ∫ x,curvatureFormEnergy (r := r) E g.form h φ V x ∂μ := by
  let A := fun x i α => coefficients (r := r) E V x (chartPt x x) (fun _ => i) α
  have hp : AEStronglyMeasurable (weightedSourcePairing (r := r) E g.form h φ f A) μ := by
    change AEStronglyMeasurable (weightedSourcePairing (r := r) E g.form h φ f
      (fun x i α => coefficients (r := r) E V x (chartPt x x) (fun _ => i) α)) μ
    rw [weightedSourcePairing_eq_weightedOnePairing]
    exact (locallyL2_weightedOnePairing_compact_integrable E g μ hμ h hh φ hφ hE f V hf hV hcV).aestronglyMeasurable
  have hq : Integrable (weightedCurvatureEnergy (r := r) E g.form h φ A) μ :=
    curvatureFormEnergy_integrable E hE g μ hμ h hh φ hφ V hV hcV
  have hb := (weightedSourcePairing_estimate E g.form μ h φ hN f A
    (weighted_inverseCurvatureNormSq_aemeasurable E hE g μ hμ h hh φ hφ f hf) hp hq hfinite).2
  change Complex.normSq (∫ x,weightedSourcePairing (r := r) E g.form h φ f
    (fun x i α => coefficients (r := r) E V x (chartPt x x) (fun _ => i) α) x ∂μ) ≤ _ at hb
  rw [weightedSourcePairing_eq_weightedOnePairing] at hb
  simpa only [Complex.normSq_eq_norm_sq,weightedOneInner,weightedCurvatureEnergy,curvatureFormEnergy,A] using hb

include hE in
theorem compact_source_joint_graph_bound
    (hN : WeightedNakanoNonnegative (r := r) E h φ)
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f)
    (hfinite : inverseCurvatureIntegral (r := r) E g.form h μ φ f < ⊤)
    (U : WeightedOneSection E g μ hμ h hh φ hφ) (hU : SmoothForm (r := r) E U.1)
    (hcU : IsCompact (closure {x | U.1 x ≠ (0 : NQForm E 1) x}))
    (D : WeightedTwoSection E g μ hμ h hh φ hφ) (hD : SmoothForm (r := r) E D.1)
    (hcD : IsCompact (closure {x | D.1 x ≠ (0 : NQForm E 2) x}))
    (hUD : SmoothDbarRepresents (r := r) E U.1 D.1)
    (S : WeightedTopSection E g μ hμ h hh φ hφ) (hS : SmoothForm (r := r) E S.1)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph) :
    ‖weightedOneInner E g.form μ h φ f U.1‖ ^ 2 ≤
      (inverseCurvatureIntegral (r := r) E g.form h μ φ f).toReal *
        (‖realizeWeightedTopSection E g μ hμ h hh φ hφ S‖ ^ 2 +
          ‖realizeWeightedTwoSection E g μ hμ h hh φ hφ D‖ ^ 2) := by
  have hb := compact_bkn_estimate E g μ hμ h hh φ hφ hE U hU hcU D.1 hD hcD hUD S hS hUS
  have hn := realizeWeightedTwoSection_norm_sq E g μ hμ h hh φ hφ D
  change ‖realizeWeightedTwoSection E g μ hμ h hh φ hφ D‖ ^ 2 =
    (weightedNormSq (r := r) E g.form h μ φ D.1).toReal at hn
  rw [← hn,add_comm] at hb
  exact (compact_source_curvature_bound E g μ hμ h hh φ hφ hE hN f hf hfinite U.1 hU hcU).trans
    (mul_le_mul_of_nonneg_left hb ENNReal.toReal_nonneg)

end Yau.LeafProofs.L14Aux
