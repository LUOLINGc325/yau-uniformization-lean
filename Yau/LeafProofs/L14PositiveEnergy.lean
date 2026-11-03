import Yau.LeafProofs.L14RaisedDerivatives
import Yau.LeafProofs.L14PositiveAlgebra
import Yau.LeafProofs.L14BundleCurvature

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def chartPositiveEnergy (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (a : M.Carrier) (z : ComplexVector n) : ℝ :=
  ((hMat g a z).det.re)⁻¹ * (positiveTensorContraction (hMat g a z)
    (weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ) z)
      (raisedBarTensor (r := r) E g u a z)).re

theorem chartPositiveEnergy_overlap (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (hu : SmoothForm (r := r) E u)
    (a b : M.Carrier) (z : ComplexVector n) (hz : z ∈ bundleChartOverlap (r := r) E a b) :
    chartPositiveEnergy (r := r) E g.form h φ u b z =
      chartPositiveEnergy (r := r) E g.form h φ u a (chartPt a (chartInv b z)) := by
  classical
  let T := fun w => chartPt a (chartInv b w)
  let J := Matrix.of fun p i => fderiv ℂ T z (stdVec i) p
  let G := hMat g.form a (T z)
  let H := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ) (T z)
  let A := bundleFrameTransitionMatrix (r := r) E b a (chartInv b z)
  let C := bundleFrameTransitionMatrix (r := r) E a b (chartInv b z)
  let D := raisedBarTensor (r := r) E g.form u a (T z)
  have hG : hMat g.form b z = Jᴴ * G * J := hMat_overlap E g.form a b z hz
  have hH : weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h b) (inChart b φ) z = Aᴴ * H * A :=
    weightedMetricMatrix_overlap E h φ a b z hz
  have hD : raisedBarTensor (r := r) E g.form u b z =
      (fun α => J.det • ∑ γ, C α γ • (Jᴴ * D γ * (J⁻¹)ᵀ)) := by
    funext α
    exact raisedBarTensor_overlap E hE g u hu a b z hz α
  unfold chartPositiveEnergy
  rw [hG, hH, hD]
  exact positiveEnergy_pullback_algebra G J H A C D (chartTransitionJacobian_det_isUnit E a b z hz)
    (bundleFrameTransitionMatrix_mul_reverse E b a (chartInv b z) hz.1.2 hz.2.2)

theorem chartPositiveEnergy_nonneg (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    0 ≤ chartPositiveEnergy (r := r) E g h φ u a z := by
  exact mul_nonneg (inv_nonneg.mpr (L18Aux.hMat_det_re_pos g a hz.1).le)
    (weighted_trace_remainder_nonneg _ _ (hMat_posDef g a z hz.1)
      (weightedMetricMatrix_posDef _ _ z (metricMatrix_posDef E h a z hz)) _)

def positiveFormEnergy (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (x : M.Carrier) : ℝ :=
  chartPositiveEnergy (r := r) E g h φ u x (chartPt x x)

theorem positiveFormEnergy_nonneg (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (x : M.Carrier) : 0 ≤ positiveFormEnergy (r := r) E g h φ u x := by
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  exact chartPositiveEnergy_nonneg E g h φ u x (chartPt x x) hz

theorem positiveFormEnergy_inChart (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (hu : SmoothForm (r := r) E u)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    positiveFormEnergy (r := r) E g.form h φ u (chartInv a z) =
      chartPositiveEnergy (r := r) E g.form h φ u a z := by
  let x := chartInv a z
  have hxx : chartInv x (chartPt x x) = x := chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hself : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [hxx]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have hoverlap : chartPt x x ∈ bundleChartOverlap (r := r) E a x := by
    refine ⟨hself, ?_⟩
    change chartInv x (chartPt x x) ∈ bundleChartSource (r := r) E a
    rw [hxx]
    exact ⟨(extChartAt (ComplexModel n) a).map_target hz.1, hz.2⟩
  have hzback : chartPt a (chartInv x (chartPt x x)) = z := by
    rw [hxx]
    exact (extChartAt (ComplexModel n) a).right_inv hz.1
  exact (chartPositiveEnergy_overlap E hE g h φ u hu a x (chartPt x x) hoverlap).trans
    (congrArg (chartPositiveEnergy (r := r) E g.form h φ u a) hzback)

theorem chartPositiveEnergy_eq_localPositiveEnergy (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u : NQForm E 1) (a : M.Carrier) (z : ComplexVector n) :
    chartPositiveEnergy (r := r) E g h φ u a z = ((hMat g a z).det.re)⁻¹ *
      localPositiveEnergy (hMat g a z)
        (weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ) z)
        (fun w i α => chartOneRaise g a (fun t j => coefficients (r := r) E u a t (fun _ => j)) w i α) z := by
  rfl

end Yau.LeafProofs.L14Aux
