import Yau.Proofs.G02LocalVolume

noncomputable section
open MeasureTheory
open scoped Topology Manifold ENNReal Matrix

namespace Yau.Proofs.G02Aux
open Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem realLinearMatrix_det (L : ComplexVector n →L[ℝ] ComplexVector n) :
    (L18Aux.realLinearMatrix L).det = L.det := by
  exact LinearMap.det_toMatrix
    (complexVector_realOrthonormalBasis n).toBasis L.toLinearMap

theorem realMetric_det_transition (h : HermitianField M)
    (a b : M.Carrier) {z : ComplexVector n}
    (hza : z ∈ chartTarget a) (hzb : chartInv a z ∈ chartSource b) :
    (realMetricFn h a z).det =
      (fderiv ℝ (L12Aux.realChartChange a b) z).det ^ 2 *
        (realMetricFn h b (L12Aux.realChartChange a b z)).det := by
  change (realMetricFn h a z).det =
    (fderiv ℝ (fun t => chartPt b (chartInv a t)) z).det ^ 2 *
      (realMetricFn h b (chartPt b (chartInv a z))).det
  rw [L18Aux.realMetricFn_chart_congruence h a b hza hzb]
  simp only [Matrix.det_mul, Matrix.det_transpose, realLinearMatrix_det]
  ring

theorem density_transition (h : HermitianField M)
    (a b : M.Carrier) {z : ComplexVector n}
    (hza : z ∈ chartTarget a) (hzb : chartInv a z ∈ chartSource b) :
    density h a z =
      ENNReal.ofReal |(fderiv ℝ (L12Aux.realChartChange a b) z).det| *
        density h b (L12Aux.realChartChange a b z) := by
  unfold density
  rw [realMetric_det_transition h a b hza hzb,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    ENNReal.ofReal_mul (abs_nonneg _)]

end Yau.Proofs.G02Aux
