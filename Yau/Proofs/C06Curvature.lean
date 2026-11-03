import Yau.Proofs.P07DistanceLeviCurvature

open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.Proofs.C06Aux

open Yau Yau.Blueprint Yau.NodeProofs Yau.NodeProofs.P07DistanceLevi
open Yau.LeafProofs Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

variable {n : ℕ}

/-- Retain the strict sign that the distance-square comparison discards. -/
theorem paired_connectionCurvature_neg (X : KahlerManifold n) (x : Pt X)
    {T V : ComplexVector n} (hT : T ≠ 0) (hV : V ≠ 0) :
    realMetricInChart X.metric.form x (chartPt x x) T
        (connectionCurvature (chartChristoffelBilin X.metric.form x) (chartPt x x) V T V) +
      realMetricInChart X.metric.form x (chartPt x x) T
        (connectionCurvature (chartChristoffelBilin X.metric.form x) (chartPt x x)
          (Complex.I • V) T (Complex.I • V)) < 0 := by
  have hh := metricSmooth_of_smoothMetric X.metric
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hT' : chartVec x x T ≠ 0 := by
    intro h
    apply hT
    exact L18Aux.chartVec_injective x x (mem_extChartAt_source x)
      (h.trans (map_zero _).symm)
  have hV' : chartVec x x V ≠ 0 := by
    intro h
    apply hV
    exact L18Aux.chartVec_injective x x (mem_extChartAt_source x)
      (h.trans (map_zero _).symm)
  have H := X.positive_bisectional_curvature x (chartVec x x T) (chartVec x x V) hT' hV'
  change 0 < paperBisectionalNumerator X.metric.form x (chartVec x x T) (chartVec x x V) at H
  have hJ : paperComplexStructure x (chartVec x x V) = chartVec x x (Complex.I • V) :=
    (L18Aux.chartVec_smul x x Complex.I V).symm
  simp only [paperBisectionalNumerator, hJ, G01Aux.paperRm_eq_realRmInChart,
    tangentCoords_chartVec x x (mem_extChartAt_source x)] at H
  rw [realMetricInChart_symm X.metric.form x (chartPt x x) T,
    connectionCurvature_pair_eq_realRmInChart X.metric.form hh x hz,
    realMetricInChart_symm X.metric.form x (chartPt x x) T,
    connectionCurvature_pair_eq_realRmInChart X.metric.form hh x hz,
    G01Aux.realRmInChart_swap_first X.metric.form x (chartPt x x) V,
    G01Aux.realRmInChart_swap_first X.metric.form x (chartPt x x) (Complex.I • V)]
  linarith

theorem paired_scaled_connectionCurvature_neg (X : KahlerManifold n) (x : Pt X)
    {T V : ComplexVector n} {s : ℝ} (hT : T ≠ 0) (hV : V ≠ 0) (hs : s ≠ 0) :
    realMetricInChart X.metric.form x (chartPt x x) T
        (connectionCurvature (chartChristoffelBilin X.metric.form x) (chartPt x x)
          (s • V) T (s • V)) +
      realMetricInChart X.metric.form x (chartPt x x) T
        (connectionCurvature (chartChristoffelBilin X.metric.form x) (chartPt x x)
          (s • (Complex.I • V)) T (s • (Complex.I • V))) < 0 := by
  rw [connectionCurvature_smul_first_third, connectionCurvature_smul_first_third,
    map_smul, map_smul]
  change s ^ 2 * _ + s ^ 2 * _ < 0
  rw [← mul_add]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hs) (paired_connectionCurvature_neg X x hT hV)

end Yau.Proofs.C06Aux
