import Yau.Proofs.P07DistanceLeviParallel
import Yau.LeafProofs.L23DistanceEnergyCurvatureForm
import Yau.Proofs.G01RmAlgebra

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P07DistanceLevi
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem connectionCurvature_pair_eq_realRmInChart
    (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (U V W Z : ComplexVector n) :
    realMetricInChart h x z (connectionCurvature (chartChristoffelBilin h x) z U V W) Z =
      G01Aux.realRmInChart h x z U V W Z := by
  rw [connectionCurvature_pair_eq_sum h hh x hz]
  simp only [G01Aux.realRmInChart, rmTensor, L12Aux.curvature4,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem paperBisectionalNumerator_nonneg (X : KahlerManifold n) (x : Pt X)
    (U V : TangentVector X.manifold x) :
    0 ≤ paperBisectionalNumerator X.metric.form x U V := by
  have hzero : tangentCoords x x (0 : TangentVector X.manifold x) = 0 := map_zero _
  by_cases hU : U = 0
  · subst U
    simp [paperBisectionalNumerator, paperRm, hzero, realCoord]
  · by_cases hV : V = 0
    · subst V
      simp [paperBisectionalNumerator, paperComplexStructure, paperRm, hzero, realCoord]
    · exact (X.positive_bisectional_curvature x U V hU hV).le

/-- The real curvature pair of the two parallel index fields has the
correct nonpositive sign from the original bisectional hypothesis. -/
theorem paired_connectionCurvature_nonpos (X : KahlerManifold n) (x : Pt X)
    (T V : ComplexVector n) :
    realMetricInChart X.metric.form x (chartPt x x) T
        (connectionCurvature (chartChristoffelBilin X.metric.form x) (chartPt x x) V T V) +
      realMetricInChart X.metric.form x (chartPt x x) T
        (connectionCurvature (chartChristoffelBilin X.metric.form x) (chartPt x x)
          (Complex.I • V) T (Complex.I • V)) ≤ 0 := by
  have hh := metricSmooth_of_smoothMetric X.metric
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have H := paperBisectionalNumerator_nonneg X x (chartVec x x T) (chartVec x x V)
  have hJ : paperComplexStructure x (chartVec x x V) = chartVec x x (Complex.I • V) := by
    exact (L18Aux.chartVec_smul x x Complex.I V).symm
  simp only [paperBisectionalNumerator, hJ, G01Aux.paperRm_eq_realRmInChart,
    tangentCoords_chartVec x x (mem_extChartAt_source x)] at H
  rw [realMetricInChart_symm X.metric.form x (chartPt x x) T,
    connectionCurvature_pair_eq_realRmInChart X.metric.form hh x hz,
    realMetricInChart_symm X.metric.form x (chartPt x x) T,
    connectionCurvature_pair_eq_realRmInChart X.metric.form hh x hz,
    G01Aux.realRmInChart_swap_first X.metric.form x (chartPt x x) V,
    G01Aux.realRmInChart_swap_first X.metric.form x (chartPt x x) (Complex.I • V)]
  linarith

theorem connectionCurvature_smul_first_third
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (z U V : ComplexVector n) (s : ℝ) :
    connectionCurvature Γ z (s • U) V (s • U) = s ^ 2 • connectionCurvature Γ z U V U := by
  simp only [← connectionCurvatureMap_apply, map_smul, ContinuousLinearMap.smul_apply, smul_smul]
  rw [pow_two]

theorem paired_scaled_connectionCurvature_nonpos (X : KahlerManifold n) (x : Pt X)
    (T V : ComplexVector n) (s : ℝ) :
    realMetricInChart X.metric.form x (chartPt x x) T
        (connectionCurvature (chartChristoffelBilin X.metric.form x) (chartPt x x)
          (s • V) T (s • V)) +
      realMetricInChart X.metric.form x (chartPt x x) T
        (connectionCurvature (chartChristoffelBilin X.metric.form x) (chartPt x x)
          (s • (Complex.I • V)) T (s • (Complex.I • V))) ≤ 0 := by
  rw [connectionCurvature_smul_first_third, connectionCurvature_smul_first_third,
    map_smul, map_smul]
  change s^2 * _ + s^2 * _ ≤ 0
  rw [← mul_add]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg s) (paired_connectionCurvature_nonpos X x T V)

end Yau.NodeProofs.P07DistanceLevi
