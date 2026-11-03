import Yau.LeafProofs.L17PotentialPositivity

open Set Metric
open scoped Matrix ComplexOrder ContDiff Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17ParabolicOperatorAux
local instance coordinateMetricTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T γ : ℝ} {hT : 0<T}

def coordinateMetricError (u : SchauderSpace P T γ hT) (q : LocalCylinder P T) :
    Matrix (Fin n) (Fin n) ℂ :=
  leviC (chartFunction u q.1 q.2.2) q.2.1+
    (q.2.2 : ℝ) • leviC (P.charts.backgroundLogDet q.1) q.2.1

theorem coordinateMetricError_eq (u : SchauderSpace P T γ hT) (q : LocalCylinder P T) :
    coordinateMetricError u q=leviC (chartFunction u q.1 q.2.2) q.2.1-
      (q.2.2 : ℂ) • pullbackRicci g (P.charts.chart q.1) q.2.1 := by
  rw [coordinateMetricError,matrixRealScalar_eq_complexScalar]
  dsimp only [pullbackRicci,BoundedChartFamily.backgroundLogDet]
  simp only [smul_neg,sub_neg_eq_add]
  rfl

theorem coordinateMetricError_isHermitian (u : SchauderSpace P T γ hT) (q : LocalCylinder P T) :
    (coordinateMetricError u q).IsHermitian := by
  have hU := (chartFunction_contDiffOn_two u q.1 q.2.2).contDiffAt
    (isOpen_ball.mem_nhds q.2.1.property)
  have hz : (q.2.1 : ComplexVector n)∈ball (0 : ComplexVector n) P.charts.radius :=
    (ball_subset_ball P.radius_lt.le) q.2.1.property
  have hB := ((P.charts.backgroundLogDet_smooth q.1).contDiffAt (isOpen_ball.mem_nhds hz)).of_le
    (by simp : (2 : ℕ∞ω)≤∞)
  exact (L22Aux.leviC_isHermitian hU).add ((L22Aux.leviC_isHermitian hB).smul (IsSelfAdjoint.all (q.2.2 : ℝ)))

theorem coordinateMetricError_quadratic_abs_le (u : SchauderSpace P T γ hT)
    (q : LocalCylinder P T) (v : ComplexVector n) :
    |(star (WithLp.ofLp v) ⬝ᵥ (coordinateMetricError u q *ᵥ WithLp.ofLp v)).re|≤
      ((‖u‖+T*backgroundLogDetHessianBudget P.charts)/2)*‖v‖^2 := by
  have hU := (chartFunction_contDiffOn_two u q.1 q.2.2).contDiffAt
    (isOpen_ball.mem_nhds q.2.1.property)
  have hz : (q.2.1 : ComplexVector n)∈ball (0 : ComplexVector n) P.charts.radius :=
    (ball_subset_ball P.radius_lt.le) q.2.1.property
  have hB : ContDiffAt ℝ 2 (P.charts.backgroundLogDet q.1) q.2.1 :=
    ((P.charts.backgroundLogDet_smooth q.1).contDiffAt (isOpen_ball.mem_nhds hz)).of_le (by simp)
  have hHu : ‖fderiv ℝ (fderiv ℝ (chartFunction u q.1 q.2.2)) q.2.1‖≤‖u‖ := by
    rw [(chartFunction_hasSecondFDerivAt u q.1 q.2.2 q.2.1.property).fderiv]
    exact (hessian_holder_bounds u).1 q
  have hHb := (backgroundLogDetHessian_bounds P.charts q.1 hz).1
  have hBudget : 0≤backgroundLogDetHessianBudget P.charts :=
    zero_le_one.trans (backgroundLogDetHessianBudget_ge_one P.charts)
  have hQ1 := (leviC_quadratic_abs_le hU v).trans
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hHu (by norm_num)) (sq_nonneg ‖v‖))
  have hQ2 := (leviC_quadratic_abs_le hB v).trans
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hHb (by norm_num)) (sq_nonneg ‖v‖))
  simp only [coordinateMetricError,Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,
    dotProduct_smul,Complex.add_re,Complex.smul_re,smul_eq_mul]
  calc
    _ ≤ |(star (WithLp.ofLp v) ⬝ᵥ (leviC (chartFunction u q.1 q.2.2) q.2.1 *ᵥ WithLp.ofLp v)).re|+
        |(q.2.2 : ℝ)*(star (WithLp.ofLp v) ⬝ᵥ (leviC (P.charts.backgroundLogDet q.1) q.2.1 *ᵥ WithLp.ofLp v)).re| := abs_add_le _ _
    _ = |(star (WithLp.ofLp v) ⬝ᵥ (leviC (chartFunction u q.1 q.2.2) q.2.1 *ᵥ WithLp.ofLp v)).re|+
        (q.2.2 : ℝ)*|(star (WithLp.ofLp v) ⬝ᵥ (leviC (P.charts.backgroundLogDet q.1) q.2.1 *ᵥ WithLp.ofLp v)).re| := by
      rw [abs_mul,abs_of_nonneg q.2.2.property.1]
    _ ≤ (‖u‖/2)*‖v‖^2+(q.2.2 : ℝ)*((backgroundLogDetHessianBudget P.charts/2)*‖v‖^2) :=
      add_le_add hQ1 (mul_le_mul_of_nonneg_left hQ2 q.2.2.property.1)
    _ ≤ (‖u‖/2)*‖v‖^2+T*((backgroundLogDetHessianBudget P.charts/2)*‖v‖^2) := by
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right q.2.2.property.2 (by positivity))
    _ = _ := by ring

theorem coordinateMetric_half_double (u : SchauderSpace P T γ hT)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (q : LocalCylinder P T) :
    let G := pullbackMatrix g (P.charts.chart q.1) q.2.1
    (G+coordinateMetricError u q).PosDef ∧
      (G+coordinateMetricError u q-(1/2 : ℂ) • G).PosSemidef ∧
      ((2 : ℂ) • G-(G+coordinateMetricError u q)).PosSemidef := by
  have hz : (q.2.1 : ComplexVector n)∈ball (0 : ComplexVector n) P.charts.radius :=
    (ball_subset_ball P.radius_lt.le) q.2.1.property
  have hG := pullbackMatrix_posDef g (P.charts.chart q.1) (P.charts.differentiable q.1)
    (P.charts.inverse_differentiable q.1) (P.charts.closedBall_source q.1 (ball_subset_closedBall hz))
  apply matrix_half_double_comparison (inv_pos.mpr (P.charts.bound_pos 0)) hG
    (coordinateMetricError_isHermitian u q)
  · intro v
    exact (matrix_quadratic_comparison
      (by simpa only [Complex.ofReal_inv] using (P.charts.comparison q.1 q.2.1 hz).1)
      (P.charts.comparison q.1 q.2.1 hz).2 v).1
  · exact coordinateMetricError_quadratic_abs_le u q
  · exact div_le_div_of_nonneg_right hSmall (by norm_num)

end Yau.LeafProofs.L17Aux
