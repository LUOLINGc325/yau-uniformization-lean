import Yau.LeafProofs.L14Transitions
import Yau.LeafProofs.L14Gauge

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

theorem bundleFrameTransitionMatrix_overlap_contDiffOn (hE : Holomorphic (r := r) E)
    (a b : M.Carrier) (α β : Fin r) :
    ContDiffOn ℂ ∞ (fun w => bundleFrameTransitionMatrix (r := r) E a b (chartInv b w) α β)
      (bundleChartOverlap (r := r) E a b) := by
  intro w hw
  exact (bundleFrameTransitionMatrix_contDiffAt E hE a b b w hw.1.1 hw.2.2 hw.1.2 α β).contDiffWithinAt

theorem bundleFrameTransitionMatrix_overlap_reverse_contDiffOn (hE : Holomorphic (r := r) E)
    (a b : M.Carrier) (α β : Fin r) :
    ContDiffOn ℂ ∞ (fun w => bundleFrameTransitionMatrix (r := r) E b a (chartInv b w) α β)
      (bundleChartOverlap (r := r) E a b) := by
  intro w hw
  exact (bundleFrameTransitionMatrix_contDiffAt E hE b a b w hw.1.1 hw.1.2 hw.2.2 α β).contDiffWithinAt

theorem curvature_overlap (hE : Holomorphic (r := r) E)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (a b : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ bundleChartOverlap (r := r) E a b) (i j : Fin n) :
    curvature (r := r) E h b z i j =
      (bundleFrameTransitionMatrix (r := r) E b a (chartInv b z))ᴴ *
        (∑ p, ∑ q, (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec i) p *
          star (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec j) q)) •
            curvature (r := r) E h a (chartPt a (chartInv b z)) p q) *
              bundleFrameTransitionMatrix (r := r) E b a (chartInv b z) := by
  let O := bundleChartOverlap (r := r) E a b
  let T := fun w => chartPt a (chartInv b w)
  let A := fun w => bundleFrameTransitionMatrix (r := r) E b a (chartInv b w)
  let C := fun w => bundleFrameTransitionMatrix (r := r) E a b (chartInv b w)
  have hO : IsOpen O := bundleChartOverlap_isOpen E a b
  have hEq : Set.EqOn (BundleDbar.metricMatrix (r := r) E h b)
      (fun w => (A w)ᴴ * BundleDbar.metricMatrix (r := r) E h a (T w) * A w) O :=
    fun w hw => metricMatrix_overlap E h a b w hw
  have hcong := congrArg (fun R => R i j)
    (curvatureMatrix_congr_of_eqOn _ _ hO hEq z hz)
  exact hcong.trans (curvatureMatrix_holomorphic_change hO (localDomain_isOpen E a)
    (BundleDbar.metricMatrix (r := r) E h a) T A C (hh a)
    (fun w hw => ((metricMatrix_posDef E h a w hw).isUnit.map Matrix.detMonoidHom).ne_zero)
    (chartTransition_bundleChartOverlap_contDiff E a b) (chartTransition_maps_bundleChartOverlap E a b)
    (bundleFrameTransitionMatrix_overlap_reverse_contDiffOn E hE a b)
    (bundleFrameTransitionMatrix_overlap_contDiffOn E hE a b)
    (fun w hw => bundleFrameTransitionMatrix_mul_reverse E b a (chartInv b w) hw.1.2 hw.2.2) z hz i j)

theorem weightedMetricMatrix_overlap (h : Metric E) (φ : M.Carrier → ℝ)
    (a b : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ bundleChartOverlap (r := r) E a b) :
    weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h b) (inChart b φ) z =
      (bundleFrameTransitionMatrix (r := r) E b a (chartInv b z))ᴴ *
        weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
          (chartPt a (chartInv b z)) *
            bundleFrameTransitionMatrix (r := r) E b a (chartInv b z) := by
  have hinv : chartInv a (chartPt a (chartInv b z)) = chartInv b z :=
    chartInv_chartPt_of_mem a _ (by simpa only [extChartAt_source] using hz.2.1)
  simp only [weightedMetricMatrix, inChart, hinv]
  rw [metricMatrix_overlap E h a b z hz, Matrix.mul_smul, Matrix.smul_mul]

theorem weightedCurvature_overlap (hE : Holomorphic (r := r) E)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (a b : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ bundleChartOverlap (r := r) E a b) (i j : Fin n) :
    weightedCurvature (r := r) E h φ b z i j =
      (bundleFrameTransitionMatrix (r := r) E b a (chartInv b z))ᴴ *
        (∑ p, ∑ q, (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec i) p *
          star (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec j) q)) •
            weightedCurvature (r := r) E h φ a (chartPt a (chartInv b z)) p q) *
              bundleFrameTransitionMatrix (r := r) E b a (chartInv b z) := by
  let O := bundleChartOverlap (r := r) E a b
  let T := fun w => chartPt a (chartInv b w)
  let A := fun w => bundleFrameTransitionMatrix (r := r) E b a (chartInv b w)
  let C := fun w => bundleFrameTransitionMatrix (r := r) E a b (chartInv b w)
  let K := fun a => weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
  let c : ℂ := Real.exp (-inChart b φ z)
  let J := fun p q => fderiv ℂ T z (stdVec i) p * star (fderiv ℂ T z (stdVec j) q)
  let R := weightedCurvature (r := r) E h φ a (T z)
  have hO : IsOpen O := bundleChartOverlap_isOpen E a b
  have hEq : Set.EqOn (K b) (fun w => (A w)ᴴ * K a (T w) * A w) O :=
    fun w hw => weightedMetricMatrix_overlap E h φ a b w hw
  have hKa (α β : Fin r) : ContDiffOn ℝ ∞ (fun w => K a w α β) (localDomain (r := r) E a) :=
    weightedMetricMatrix_contDiffOn _ _ (hh a) ((hφ a).mono Set.inter_subset_left) α β
  have hdet : ∀ w ∈ localDomain (r := r) E a, (K a w).det ≠ 0 := fun w hw =>
    ((weightedMetricMatrix_posDef _ _ w (metricMatrix_posDef E h a w hw)).isUnit.map Matrix.detMonoidHom).ne_zero
  have hc := (congrArg (fun Q => Q i j)
    (curvatureMatrix_congr_of_eqOn _ _ hO hEq z hz)).trans
      (curvatureMatrix_holomorphic_change hO (localDomain_isOpen E a) (K a) T A C hKa hdet
        (chartTransition_bundleChartOverlap_contDiff E a b) (chartTransition_maps_bundleChartOverlap E a b)
        (bundleFrameTransitionMatrix_overlap_reverse_contDiffOn E hE a b)
        (bundleFrameTransitionMatrix_overlap_contDiffOn E hE a b)
        (fun w hw => bundleFrameTransitionMatrix_mul_reverse E b a (chartInv b w) hw.1.2 hw.2.2) z hz i j)
  have hTa : T z ∈ localDomain (r := r) E a := chartTransition_maps_bundleChartOverlap E a b hz
  have hρ : (Real.exp (-inChart a φ (T z)) : ℂ) = c := by
    dsimp only [T, c, inChart]
    rw [chartInv_chartPt_of_mem a _ (by simpa only [extChartAt_source] using hz.2.1)]
  change curvatureMatrix (K b) z i j = (A z)ᴴ *
    (∑ p, ∑ q, J p q • curvatureMatrix (K a) (T z) p q) * A z at hc
  dsimp only [K] at hc
  rw [weightedMetricMatrix_curvature_inChart E h hh φ hφ b z hz.1 i j] at hc
  simp_rw [weightedMetricMatrix_curvature_inChart E h hh φ hφ a (T z) hTa, hρ] at hc
  have hsum : (∑ p, ∑ q, J p q • (c • R p q)) = c • (∑ p, ∑ q, J p q • R p q) := by
    simp only [Finset.smul_sum, smul_smul, mul_comm]
  change c • weightedCurvature (r := r) E h φ b z i j =
    (A z)ᴴ * (∑ p, ∑ q, J p q • (c • R p q)) * A z at hc
  rw [hsum, Matrix.mul_smul, Matrix.smul_mul] at hc
  have hcne : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have he := congrArg (fun B : Matrix (Fin r) (Fin r) ℂ => c⁻¹ • B) hc
  simpa only [smul_smul, inv_mul_cancel₀ hcne, one_smul] using he

end Yau.LeafProofs.L14Aux
