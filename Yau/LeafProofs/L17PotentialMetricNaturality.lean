import Yau.LeafProofs.L17CoordinateMetric

open Set Metric
open scoped Matrix ComplexOrder ContDiff Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17ParabolicOperatorAux
local instance potentialMetricNaturalityTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T γ : ℝ} {hT : 0<T}

def potentialMetricMatrix (u : SchauderSpace P T γ hT) (q : Cylinder M T) :
    Matrix (Fin n) (Fin n) ℂ :=
  gMat g q.1+levi (fun y => schauderFun u (y,q.2)) q.1-(q.2 : ℂ) • ricci g q.1

theorem coordinateMetricMatrix_eq_congruence (hg : MetricSmooth g)
    (u : SchauderSpace P T γ hT) (q : LocalCylinder P T) :
    let J := linearMatrix (coordinateDifferential (P.charts.chart q.1)
      (P.charts.chart q.1 q.2.1) q.2.1)
    pullbackMatrix g (P.charts.chart q.1) q.2.1+coordinateMetricError u q=
      Jᴴ*potentialMetricMatrix u (chartPoint P T q.1 q.2)*J := by
  let e := P.charts.chart q.1
  let z : ComplexVector n := q.2.1
  let x : M.Carrier := e z
  let J := linearMatrix (coordinateDifferential e x z)
  have hz : z∈e.source := P.charts.closedBall_source q.1
    (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) q.2.1.property))
  have hG : pullbackMatrix g e z=Jᴴ*gMat g x*J :=
    pullbackMatrix_eq_congruence g e x z (mem_extChartAt_source x)
  have hR : pullbackRicci g e z=Jᴴ*ricci g x*J :=
    pullbackRicci_eq_ricci g hg e (P.charts.differentiable q.1)
      (P.charts.inverse_differentiable q.1) hz
  have hL : leviC (chartFunction u q.1 q.2.2) z=
      Jᴴ*levi (fun y => schauderFun u (y,q.2.2)) x*J :=
    leviC_backgroundChart_pullback e (P.charts.differentiable q.1)
      (fun y => schauderFun u (y,q.2.2)) hz (actualFunction_native_contDiffAt u x q.2.2)
  change pullbackMatrix g e z+coordinateMetricError u q=
    Jᴴ*(gMat g x+levi (fun y => schauderFun u (y,q.2.2)) x-(q.2.2 : ℂ) • ricci g x)*J
  rw [coordinateMetricError_eq,hG,hL,hR]
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul]
  abel

theorem coordinateMetricMatrix_determinant_ratio (hg : MetricSmooth g)
    (u : SchauderSpace P T γ hT) (q : LocalCylinder P T) :
    (pullbackMatrix g (P.charts.chart q.1) q.2.1+coordinateMetricError u q).det.re/
        (pullbackMatrix g (P.charts.chart q.1) q.2.1).det.re=
      (potentialMetricMatrix u (chartPoint P T q.1 q.2)).det.re/
        (gMat g (chartPoint P T q.1 q.2).1).det.re := by
  let e := P.charts.chart q.1
  let z : ComplexVector n := q.2.1
  let x : M.Carrier := e z
  let J := linearMatrix (coordinateDifferential e x z)
  have hz : z∈e.source := P.charts.closedBall_source q.1
    (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) q.2.1.property))
  rw [coordinateMetricMatrix_eq_congruence hg u q]
  have hG : pullbackMatrix g e z=Jᴴ*gMat g x*J :=
    pullbackMatrix_eq_congruence g e x z (mem_extChartAt_source x)
  change (Jᴴ*potentialMetricMatrix u (chartPoint P T q.1 q.2)*J).det.re/
    (pullbackMatrix g e z).det.re=_
  rw [hG]
  exact determinant_ratio_congruence _ _ J (linearMatrix_det_ne_zero _
    (coordinateDifferential_injective e (P.charts.differentiable q.1)
      (P.charts.inverse_differentiable q.1) x hz (mem_extChartAt_source x)))

end Yau.LeafProofs.L17Aux
