import Yau.LeafProofs.L23TensorPermutation
import Yau.LeafProofs.L23TensorTraceFrame

/-! Ricci is the genuine trace of the original curvature in every chart. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

def ricciTraceSlots : Equiv.Perm (Fin 4) where
  toFun s := ![0,2,3,1] s
  invFun s := ![0,3,1,2] s
  left_inv s := by fin_cases s <;> rfl
  right_inv s := by fin_cases s <;> rfl

variable {n : ℕ} {M : ComplexManifold n}

theorem realRicciCoeff_eq_tensorMetricTrace (h : HermitianField M)
    (c : M.Carrier) (z : ComplexVector n) (v : Fin 2 → RIdx n) :
    realRicciCoeff h c z (v 0) (v 1)=
      tensorMetricTrace (realMetricFn h c z)⁻¹
        (fun w => rmTensor h c z (w ∘ ricciTraceSlots)) v := by
  rfl

theorem realRicciTensor_chart_change (h : HermitianField M) (hh : MetricSmooth h)
    (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    (fun v : Fin 2 → RIdx n => realRicciCoeff h c z (v 0) (v 1))=
      tensorFrameTransform (realChartJacobian c d z)
        (fun v : Fin 2 → RIdx n =>
          realRicciCoeff h d (L12Aux.realChartChange c d z) (v 0) (v 1)) := by
  have hr : (fun w => rmTensor h c z (w ∘ ricciTraceSlots))=
      tensorFrameTransform (realChartJacobian c d z)
        (fun w => rmTensor h d (L12Aux.realChartChange c d z) (w ∘ ricciTraceSlots)) := by
    rw [rmTensor_chart_change h hh c d hz hy]
    exact tensorFrameTransform_permute _ _ _
  funext v
  rw [realRicciCoeff_eq_tensorMetricTrace,hr,tensorMetricTrace_frameTransform,
    inverseMetric_chart_change h c d hz hy]
  rfl

theorem realRicciCoeff_chart_change (h : HermitianField M) (hh : MetricSmooth h)
    (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source)
    (i j : RIdx n) :
    realRicciCoeff h c z i j=∑ a, ∑ b,
      realChartJacobian c d z a i*realRicciCoeff h d (L12Aux.realChartChange c d z) a b*
        realChartJacobian c d z b j := by
  have heq := congrFun (realRicciTensor_chart_change h hh c d hz hy) ![i,j]
  simp only [tensorFrameTransform,sum_tensor_cons,Fin.prod_univ_succ,Fin.prod_univ_zero,
    Fin.cons_zero,Fin.cons_succ,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons,Matrix.tail_cons,mul_one,Fintype.sum_unique] at heq
  convert heq using 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change realChartJacobian c d z a i*
      realRicciCoeff h d (L12Aux.realChartChange c d z) a b*realChartJacobian c d z b j=
    realRicciCoeff h d (L12Aux.realChartChange c d z) a b*
      (realChartJacobian c d z a i*realChartJacobian c d z b j)
  ring

end Yau.LeafProofs.L23Aux
