import Yau.LeafProofs.L23DistanceEnergyCovariant
import Yau.LeafProofs.L23FieldMetricParallelCalculus
import Yau.LeafProofs.L23TensorMultilinear

/-! Pullback-connection curvature is exactly the frozen riemannCoeff and rmTensor. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
open L12Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {n : ℕ} {M : ComplexManifold n}

theorem chartChristoffelBilin_derivative_basis (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z∈chartTarget c) (a i j : RIdx n) :
    fderiv ℝ (chartChristoffelBilin h c) z (realVec a) (realVec i) (realVec j)=
      ∑ l, rDeriv (fun w => christoffel h c w l i j) z a • realVec l := by
  have hΓ : DifferentiableAt ℝ (chartChristoffelBilin h c) z :=
    ((chartChristoffelBilin_contDiffOn h hh c).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hd (l : RIdx n) : DifferentiableAt ℝ (fun w => christoffel h c w l i j) z :=
    ((christoffel_contDiffOn h hh c l i j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hEval := ((hΓ.hasFDerivAt.clm_apply (hasFDerivAt_const (realVec i) z)).clm_apply
    (hasFDerivAt_const (realVec j) z)).fderiv
  have he : fderiv ℝ (fun w => chartChristoffelBilin h c w (realVec i) (realVec j)) z (realVec a)=
      fderiv ℝ (chartChristoffelBilin h c) z (realVec a) (realVec i) (realVec j) := by
    rw [hEval]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_zero,zero_add,
      ContinuousLinearMap.zero_apply,ContinuousLinearMap.flip_apply]
  rw [←he,show (fun w => chartChristoffelBilin h c w (realVec i) (realVec j))=
      (fun w => ∑ l, christoffel h c w l i j • realVec l) from
        funext (fun w => chartChristoffelBilin_basis h c w i j),
    fderiv_fun_sum (fun l _ => (hd l).smul_const (realVec l))]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [fderiv_smul_const (hd l)]
  rfl

theorem connectionCurvature_basis (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z∈chartTarget c) (i j k : RIdx n) :
    connectionCurvature (chartChristoffelBilin h c) z (realVec i) (realVec j) (realVec k)=
      ∑ l, riemannCoeff h c z i j k l • realVec l := by
  unfold connectionCurvature
  rw [chartChristoffelBilin_derivative_basis h hh c hz i j k,
    chartChristoffelBilin_derivative_basis h hh c hz j i k]
  simp only [chartChristoffelBilin_basis,map_sum,map_smul,Finset.smul_sum,smul_smul]
  apply realCoord_injective n
  funext l
  rw [realCoord_sum_realVec]
  rw [←realCoordCLM_apply l]
  simp only [map_sub,map_add,map_sum,map_smul,realCoordCLM_apply,realCoord_realVec,smul_eq_mul]
  simp [riemannCoeff,Finset.sum_sub_distrib,mul_comm,mul_left_comm,mul_assoc]
  <;> ring

theorem connectionCurvature_pair_basis (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z∈chartTarget c) (i j k l : RIdx n) :
    realMetricInChart h c z
      (connectionCurvature (chartChristoffelBilin h c) z (realVec i) (realVec j) (realVec k)) (realVec l)=
        rmTensor h c z ![i,j,k,l] := by
  rw [connectionCurvature_basis h hh c hz]
  simp only [map_sum,sum_apply,map_smul,smul_apply,smul_eq_mul,realMetricInChart_basis h c z hz]
  change (∑ p, riemannCoeff h c z i j k p*realMetricFn h c z p l)=
    ∑ p, realMetricFn h c z p l*riemannCoeff h c z i j k p
  apply Finset.sum_congr rfl
  intro p _
  ring

end Yau.LeafProofs.L23Aux
