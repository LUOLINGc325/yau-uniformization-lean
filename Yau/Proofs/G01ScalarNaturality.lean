import Yau.Blueprint.NormalizationTargets
import Yau.LeafProofs.L23RicciNaturality

noncomputable section
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.G01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual double inverse-metric contraction is invariant under the actual chart Jacobian. -/
theorem realScalarCurvatureInChart_change (h : HermitianField M) (hs : MetricSmooth h)
    (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    Blueprint.realScalarCurvatureInChart h c z =
      Blueprint.realScalarCurvatureInChart h d (L12Aux.realChartChange c d z) := by
  unfold Blueprint.realScalarCurvatureInChart
  simp_rw [L23Aux.realRicciCoeff_chart_change h hs c d hz hy]
  have hG := L23Aux.inverseMetric_chart_change h c d hz hy
  calc
    _ = ∑ a, ∑ b,
        (L23Aux.realChartJacobian c d z * (realMetricFn h c z)⁻¹ *
          (L23Aux.realChartJacobian c d z)ᵀ) a b *
        realRicciCoeff h d (L12Aux.realChartChange c d z) a b := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum,
        Finset.sum_mul]
      conv_lhs =>
        arg 2
        ext i
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      conv_lhs =>
        arg 2
        ext i
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hG]

end Yau.NodeProofs.G01Aux
