import Yau.LeafProofs.L23TensorChart

/-! Coordinate changes for the actual real metric and its inverse. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
open L12Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def realLinearMatrix (L : ComplexVector n →L[ℝ] ComplexVector n) :
    Matrix (RIdx n) (RIdx n) ℝ := fun a i => realCoord (L (realVec i)) a

theorem realLinearMatrix_mul (L K : ComplexVector n →L[ℝ] ComplexVector n) :
    realLinearMatrix L*realLinearMatrix K=realLinearMatrix (L.comp K) := by
  ext i j
  simp only [realLinearMatrix,Matrix.mul_apply,ContinuousLinearMap.comp_apply]
  calc
    _=∑ a, realCoord (K (realVec j)) a*realCoord (L (realVec a)) i := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _=realCoord (L (K (realVec j))) i := by
      have heq := congrArg (fun v => (realCoordCLM i) (L v))
        (sum_realCoord_realVec (K (realVec j)))
      simpa only [map_sum,map_smul,smul_eq_mul,realCoordCLM_apply] using heq

theorem realLinearMatrix_id :
    realLinearMatrix (ContinuousLinearMap.id ℝ (ComplexVector n))=1 := by
  ext i j
  simp [realLinearMatrix,realCoord_realVec,Matrix.one_apply,eq_comm]

def realChartJacobian (c d : M.Carrier) (z : ComplexVector n) :
    Matrix (RIdx n) (RIdx n) ℝ :=
  realLinearMatrix (fderiv ℝ (realChartChange c d) z)

theorem realChartJacobian_left_inverse (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    realChartJacobian d c (realChartChange c d z)*realChartJacobian c d z=1 := by
  rw [realChartJacobian,realChartJacobian,realLinearMatrix_mul]
  have hi : (fderiv ℝ (realChartChange d c) (realChartChange c d z)).comp
      (fderiv ℝ (realChartChange c d) z)=ContinuousLinearMap.id ℝ (ComplexVector n) := by
    apply ContinuousLinearMap.ext
    intro v
    exact realChartChange_fderiv_inverse c d hz hy v
  rw [hi,realLinearMatrix_id]

theorem realMetricInChart_change (h : HermitianField M) (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source)
    (u v : ComplexVector n) :
    realMetricInChart h c z u v=
      realMetricInChart h d (realChartChange c d z)
        (fderiv ℝ (realChartChange c d) z u) (fderiv ℝ (realChartChange c d) z v) := by
  have hzD : realChartChange c d z ∈ chartTarget d :=
    (extChartAt (ComplexModel n) d).map_source hy
  have hbInv : chartInv d (realChartChange c d z)=chartInv c z :=
    (extChartAt (ComplexModel n) d).left_inv hy
  have hBr : chartInv c z ∈ (chartAt (ComplexVector n) d).source := by
    simpa only [extChartAt_source] using hy
  rw [realMetricInChart_apply,realMetricInChart_apply,
    ←realCoordinateField_eq_realChartVec c z u hz,
    ←realCoordinateField_eq_realChartVec c z v hz,
    ←realCoordinateField_eq_realChartVec d _ _ hzD,
    ←realCoordinateField_eq_realChartVec d _ _ hzD,hbInv,
    ←realFrameCLM_apply d _ hBr,←realFrameCLM_apply d _ hBr,
    realChartChange_frame c d hz hy u,realChartChange_frame c d hz hy v]

theorem realMetricFn_chart_change_entry (h : HermitianField M) (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source)
    (i j : RIdx n) :
    realMetricFn h c z i j=∑ a, ∑ b,
      realChartJacobian c d z a i*realMetricFn h d (realChartChange c d z) a b*
        realChartJacobian c d z b j := by
  rw [←realMetricInChart_basis h c z hz i j,
    realMetricInChart_change h c d hz hy,realBilin_eq_sum]
  have hzD : realChartChange c d z ∈ chartTarget d :=
    (extChartAt (ComplexModel n) d).map_source hy
  simp only [realMetricInChart_basis h d _ hzD,realChartJacobian,realLinearMatrix]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem realMetricFn_chart_change (h : HermitianField M) (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    realMetricFn h c z=(realChartJacobian c d z)ᵀ*
      realMetricFn h d (realChartChange c d z)*realChartJacobian c d z := by
  ext i j
  rw [realMetricFn_chart_change_entry h c d hz hy]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem inverseMetric_chart_change (h : HermitianField M) (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    realChartJacobian c d z*(realMetricFn h c z)⁻¹*(realChartJacobian c d z)ᵀ=
      (realMetricFn h d (realChartChange c d z))⁻¹ := by
  let J := realChartJacobian c d z
  have hJ : IsUnit J.det := Matrix.isUnit_det_of_left_inverse
    (realChartJacobian_left_inverse c d hz hy)
  have hJT := Matrix.isUnit_det_transpose J hJ
  rw [realMetricFn_chart_change h c d hz hy,Matrix.mul_inv_rev,Matrix.mul_inv_rev]
  change J*(J⁻¹*((realMetricFn h d (realChartChange c d z))⁻¹*Jᵀ⁻¹))*Jᵀ=_
  rw [←Matrix.mul_assoc,←Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hJ,
    Matrix.one_mul,Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hJT,Matrix.mul_one]

end Yau.LeafProofs.L23Aux
