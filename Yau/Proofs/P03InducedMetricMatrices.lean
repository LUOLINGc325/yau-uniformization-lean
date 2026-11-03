import Yau.Proofs.P03MetricDescent

open scoped Manifold Topology ContDiff ComplexOrder Matrix TensorProduct
open Yau.LeafProofs

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar
open scoped CoefficientNorms CoefficientBundles

variable {n : ℕ} {M : ComplexManifold n}

theorem antiCanonicalCoordinate_symm_stdVec (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (i : Fin 1) :
    (antiCanonicalCoordinateEquiv a x hx).symm (stdVec i) = chartTopEvaluation a x hx := by
  apply (antiCanonicalCoordinateEquiv a x hx).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext j : 1
  rw [antiCanonicalCoordinateEquiv_apply, chartTopEvaluation_topForm]
  have hj : j = i := Subsingleton.elim _ _
  subst j
  simp [stdVec]

theorem antiCanonical_metricMatrix (g : HermitianField M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    BundleDbar.metricMatrix (r := 1) (AntiCanonicalFiber M) (antiCanonicalMetric g) a z =
      antiCanonicalMetricMatrix g a z := by
  have hx : chartInv a z ∈ (extChartAt (ComplexModel n) a).source :=
    (extChartAt (ComplexModel n) a).map_target hz
  have hi : chartPt a (chartInv a z) = z := (extChartAt (ComplexModel n) a).right_inv hz
  ext i j
  dsimp only [BundleDbar.metricMatrix, localTriv, antiCanonicalMetricMatrix]
  rw [antiCanonical_trivialization_symmL a (chartInv a z) hx,
    antiCanonical_trivialization_symmL a (chartInv a z) hx,
    antiCanonicalCoordinate_symm_stdVec a _ hx i,
    antiCanonicalCoordinate_symm_stdVec a _ hx j,
    antiCanonicalMetric_chart_apply g a _ hx]
  simp only [chartTopEvaluation_topForm, star_one, one_mul, mul_one]
  change (hMat g a (chartPt a (chartInv a z))).det = (hMat g a z).det
  rw [hi]

theorem tangentAntiCanonical_metricMatrix (g : HermitianField M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    BundleDbar.metricMatrix (r := n) (TangentAntiCanonicalFiber M) (tangentAntiCanonicalMetric g) a z =
      tangentAntiCanonicalMetricMatrix g a z := by
  have hx : chartInv a z ∈ (extChartAt (ComplexModel n) a).source :=
    (extChartAt (ComplexModel n) a).map_target hz
  have hi : chartPt a (chartInv a z) = z := (extChartAt (ComplexModel n) a).right_inv hz
  ext i j
  dsimp only [BundleDbar.metricMatrix, localTriv, tangentAntiCanonicalMetricMatrix]
  rw [tangentAntiCanonical_trivialization_symmL a (chartInv a z) hx,
    tangentAntiCanonical_trivialization_symmL a (chartInv a z) hx]
  change (tangentAntiCanonicalMetric g (chartInv a z)).toFun
      ((tangentAntiCanonicalCoordinateLinearEquiv a _ hx).symm (stdVec i))
      ((tangentAntiCanonicalCoordinateLinearEquiv a _ hx).symm (stdVec j)) = _
  rw [tangentAntiCanonicalCoordinateLinearEquiv_symm,
    tangentAntiCanonicalCoordinateLinearEquiv_symm,
    tangentAntiCanonicalMetric_tmul, antiCanonicalMetric_chart_apply g a _ hx]
  simp only [chartTopEvaluation_topForm, star_one, one_mul, mul_one]
  rw [hi]
  rfl

theorem antiCanonical_metric_smooth (g : Yau.SmoothMetric M) :
    BundleDbar.SmoothMetric (r := 1) (AntiCanonicalFiber M) (antiCanonicalMetric g.form) := by
  intro a α β
  rw [antiCanonical_localDomain]
  apply (L18Aux.contDiffOn_matrix_det (L18Aux.hMat_contDiffOn g a)).congr
  intro z hz
  exact congrFun (congrFun (antiCanonical_metricMatrix g.form a hz) α) β

theorem tangentAntiCanonical_metric_smooth (g : Yau.SmoothMetric M) :
    BundleDbar.SmoothMetric (r := n) (TangentAntiCanonicalFiber M)
      (tangentAntiCanonicalMetric g.form) := by
  intro a α β
  rw [tangentAntiCanonical_localDomain]
  apply ((L18Aux.contDiffOn_matrix_det (L18Aux.hMat_contDiffOn g a)).mul
    (L18Aux.hMat_contDiffOn g a α β)).congr
  intro z hz
  exact congrFun (congrFun (tangentAntiCanonical_metricMatrix g.form a hz) α) β

end Yau.NodeProofs.P03Aux
