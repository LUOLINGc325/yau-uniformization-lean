import Yau.LeafProofs.L23FieldMetricFirstVariation

/-! The physical, regularized radius in a fixed coordinate tangent space. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def chartVectorNorm (h : HermitianField M) (c : M.Carrier) (z v : ComplexVector n) : ℝ :=
  Real.sqrt (realMetricInChart h c z v v)

theorem chartVectorNorm_eq_norm (h : HermitianField M) (c : M.Carrier)
    (z v : ComplexVector n) :
    letI := underlyingRealTangentNormedAddCommGroup h (chartInv c z)
    chartVectorNorm h c z v = ‖realChartVec c z v‖ := by
  letI := underlyingRealTangentNormedAddCommGroup h (chartInv c z)
  letI := underlyingRealTangentInnerProductSpace h (chartInv c z)
  change Real.sqrt (inner ℝ (realChartVec c z v) (realChartVec c z v)) = ‖realChartVec c z v‖
  rw [real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]

theorem realMetricInChart_quadratic_nonneg (h : HermitianField M) (c : M.Carrier)
    (z v : ComplexVector n) : 0 ≤ realMetricInChart h c z v v := by
  letI := underlyingRealTangentNormedAddCommGroup h (chartInv c z)
  letI := underlyingRealTangentInnerProductSpace h (chartInv c z)
  change 0 ≤ inner ℝ (realChartVec c z v) (realChartVec c z v)
  exact real_inner_self_nonneg

theorem chartVectorNorm_sq (h : HermitianField M) (c : M.Carrier) (z v : ComplexVector n) :
    chartVectorNorm h c z v ^ 2 = realMetricInChart h c z v v :=
  Real.sq_sqrt (realMetricInChart_quadratic_nonneg h c z v)

theorem realMetricInChart_abs_le_chartVectorNorm (h : HermitianField M) (c : M.Carrier)
    (z v w : ComplexVector n) :
    |realMetricInChart h c z v w| ≤ chartVectorNorm h c z v*chartVectorNorm h c z w := by
  letI := underlyingRealTangentNormedAddCommGroup h (chartInv c z)
  letI := underlyingRealTangentInnerProductSpace h (chartInv c z)
  rw [chartVectorNorm_eq_norm,chartVectorNorm_eq_norm]
  exact abs_real_inner_le_norm (realChartVec c z v) (realChartVec c z w)

def regularizedChartRadius (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (d : ℝ) (v : ComplexVector n) : ℝ :=
  Real.sqrt (realMetricInChart h c z v v+d^2)

theorem regularizedChartRadius_pos (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) {d : ℝ} (hd : 0 < d) (v : ComplexVector n) :
    0 < regularizedChartRadius h c z d v := by
  apply Real.sqrt_pos.mpr
  exact add_pos_of_nonneg_of_pos (realMetricInChart_quadratic_nonneg h c z v) (sq_pos_of_pos hd)

theorem chartVectorNorm_le_regularizedChartRadius (h : HermitianField M) (c : M.Carrier)
    (z v : ComplexVector n) (d : ℝ) :
    chartVectorNorm h c z v ≤ regularizedChartRadius h c z d v :=
  Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg d))

theorem regularizedChartRadius_hasDerivAt (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) {d : ℝ} (hd : 0 < d)
    {a : ℝ → ComplexVector n} {a' : ComplexVector n} {t : ℝ} (ha : HasDerivAt a a' t) :
    HasDerivAt (fun s => regularizedChartRadius h c z d (a s))
      (realMetricInChart h c z (a t) a'/regularizedChartRadius h c z d (a t)) t := by
  have H := ((hasDerivAt_const t (realMetricInChart h c z)).clm_apply ha).clm_apply ha
  have HQ : HasDerivAt (fun s => realMetricInChart h c z (a s) (a s))
      (2*realMetricInChart h c z (a t) a') t := by
    convert! H using 1
    simp only [ContinuousLinearMap.zero_apply,zero_add]
    rw [realMetricInChart_symm h c z a' (a t)]
    ring
  have hpos : 0 < realMetricInChart h c z (a t) (a t)+d^2 :=
    add_pos_of_nonneg_of_pos (realMetricInChart_quadratic_nonneg h c z (a t)) (sq_pos_of_pos hd)
  have HS := (HQ.add_const (d^2)).sqrt hpos.ne'
  convert! HS using 1
  change _/regularizedChartRadius h c z d (a t) =
    (2*realMetricInChart h c z (a t) a')/(2*regularizedChartRadius h c z d (a t))
  field_simp [(regularizedChartRadius_pos h c z hd (a t)).ne']

theorem regularizedChartRadius_contDiff (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) {d : ℝ} (hd : 0 < d) :
    ContDiff ℝ ∞ (regularizedChartRadius h c z d) := by
  have HQ : ContDiff ℝ ∞ (fun v => realMetricInChart h c z v v) :=
    (contDiff_const.clm_apply contDiff_id).clm_apply contDiff_id
  exact (HQ.add contDiff_const).sqrt (fun v =>
    (add_pos_of_nonneg_of_pos (realMetricInChart_quadratic_nonneg h c z v) (sq_pos_of_pos hd)).ne')

end Yau.LeafProofs.L23Aux
