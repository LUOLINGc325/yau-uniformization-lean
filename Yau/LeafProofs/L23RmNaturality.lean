import Yau.LeafProofs.L23CurvatureNaturality
import Yau.LeafProofs.L23MetricNaturality

/-! Naturality of the fully covariant curvature defined in ParabolicCalculus. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
open L12Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def curvatureVector (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n)
    (i j k : RIdx n) : ComplexVector n :=
  ∑ p, riemannCoeff h c z i j k p • realVec p

theorem curvatureVector_coord (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n)
    (i j k ell : RIdx n) :
    realCoord (curvatureVector h c z i j k) ell=riemannCoeff h c z i j k ell :=
  realCoord_sum_realVec _ ell

theorem curvatureVector_chart_change (h : HermitianField M) (hh : MetricSmooth h)
    (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source)
    (i j k : RIdx n) :
    fderiv ℝ (realChartChange c d) z (curvatureVector h c z i j k)=
      ∑ a, ∑ b, ∑ e,
        (realChartJacobian c d z a i*realChartJacobian c d z b j*
          realChartJacobian c d z e k) •
            curvatureVector h d (realChartChange c d z) a b e := by
  apply realCoord_injective n
  funext ell
  rw [←realCoordCLM_apply,←realCoordCLM_apply]
  change (realCoordCLM ell) (fderiv ℝ (realChartChange c d) z
    (∑ p, riemannCoeff h c z i j k p • realVec p))=(realCoordCLM ell) _
  simp only [map_sum,map_smul,smul_eq_mul,realCoordCLM_apply,curvatureVector_coord]
  convert riemannCoeff_chart_change h hh c d hz hy i j k ell using 1
  · apply Finset.sum_congr rfl
    intro p _
    ring
  · rfl

theorem rmTensor_bilinear (h : HermitianField M) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (i j k l : RIdx n) :
    rmTensor h c z ![i,j,k,l]=
      realMetricInChart h c z (curvatureVector h c z i j k) (realVec l) := by
  simp only [curvatureVector,map_sum,map_smul,sum_apply,
    smul_apply,smul_eq_mul,realMetricInChart_basis h c z hz]
  change (∑ p, realMetricFn h c z p l*riemannCoeff h c z i j k p)=_
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem rmTensor_chart_change_four (h : HermitianField M) (hh : MetricSmooth h)
    (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source)
    (i j k l : RIdx n) :
    rmTensor h c z ![i,j,k,l]=∑ a, ∑ b, ∑ e, ∑ q,
      rmTensor h d (realChartChange c d z) ![a,b,e,q]*
        realChartJacobian c d z a i*realChartJacobian c d z b j*
          realChartJacobian c d z e k*realChartJacobian c d z q l := by
  have hzD : realChartChange c d z ∈ chartTarget d :=
    (extChartAt (ComplexModel n) d).map_source hy
  rw [rmTensor_bilinear h c hz,realMetricInChart_change h c d hz hy,
    curvatureVector_chart_change h hh c d hz hy]
  conv_lhs =>
    arg 2
    rw [←sum_realCoord_realVec (fderiv ℝ (realChartChange c d) z (realVec l))]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    arg 2
    ext b
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro q _
  rw [←rmTensor_bilinear h d hzD]
  unfold realChartJacobian realLinearMatrix
  ring

theorem rmTensor_chart_change (h : HermitianField M) (hh : MetricSmooth h)
    (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    rmTensor h c z=tensorFrameTransform (realChartJacobian c d z)
      (rmTensor h d (realChartChange c d z)) := by
  funext v
  have hv : v=![v 0,v 1,v 2,v 3] := by funext s; fin_cases s <;> rfl
  rw [hv,rmTensor_chart_change_four h hh c d hz hy]
  simp [tensorFrameTransform,sum_tensor_cons,Fin.prod_univ_succ,mul_assoc]
  rfl

end Yau.LeafProofs.L23Aux
