import Yau.LeafProofs.L23TensorTraceAlgebra
import Yau.LeafProofs.L23CurvatureCalculus

/-! Spatial covariant differentiation commutes with an actual inverse-
metric contraction; all contracted-slot derivatives are retained. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
open L18Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {M : ComplexManifold n}

theorem tensorMetricTrace_rDeriv
    (H : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (A : ComplexVector n → CovTensor n (r+2)) (z : ComplexVector n)
    (hH : ∀ a b, DifferentiableAt ℝ (fun w => H w a b) z)
    (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z) (i : RIdx n) (v : Fin r → RIdx n) :
    rDeriv (fun w => tensorMetricTrace (H w) (A w) v) z i=
      tensorMetricTrace (H z) (fun u => rDeriv (fun w => A w u) z i) v+
        tensorMetricTrace (fun a b => rDeriv (fun w => H w a b) z i) (A z) v := by
  have hterm (a b : RIdx n) := (hH a b).mul (hA (Fin.cons a (Fin.cons b v)))
  have hinner (a : RIdx n) : DifferentiableAt ℝ
      (fun w => ∑ b, H w a b*A w (Fin.cons a (Fin.cons b v))) z :=
    DifferentiableAt.fun_sum (fun b _ => hterm a b)
  unfold tensorMetricTrace
  calc
    _=∑ a, rDeriv (fun w => ∑ b, H w a b*A w (Fin.cons a (Fin.cons b v))) z i :=
      rDeriv_sum _ hinner i
    _=∑ a, ∑ b, rDeriv (fun w => H w a b*A w (Fin.cons a (Fin.cons b v))) z i := by
      apply Finset.sum_congr rfl
      intro a _
      exact rDeriv_sum _ (fun b => hterm a b) i
    _=∑ a, ∑ b, (rDeriv (fun w => H w a b) z i*A z (Fin.cons a (Fin.cons b v))+
        H z a b*rDeriv (fun w => A w (Fin.cons a (Fin.cons b v))) z i) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact rDeriv_mul (hH a b) (hA _) i
    _=_ := by simp only [Finset.sum_add_distrib]; ring

theorem covariantD_tensorMetricTrace (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n (r+2))
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z) (i : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c (fun w => tensorMetricTrace (realMetricFn h c w)⁻¹ (A w)) z (Fin.cons i v)=
      ∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
        covariantD h c A z (Fin.cons i (Fin.cons a (Fin.cons b v))) := by
  let H := (realMetricFn h c z)⁻¹
  let D := L12Aux.connectionMatrix h c z i
  have hInv (a b : RIdx n) := ((realMetricFn_inverse_contDiffOn h hh c a b).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hd := tensorMetricTrace_rDeriv (fun w => (realMetricFn h c w)⁻¹) A z hInv hA i v
  have hdot : (fun a b => rDeriv (fun w => (realMetricFn h c w)⁻¹ a b) z i)=
      -(D*H+H*Dᵀ) := inverseMetric_directional_derivative h hh c hz i
  rw [hdot] at hd
  have hneg : tensorMetricTrace (-(D*H+H*Dᵀ)) (A z) v=
      -tensorMetricTrace (D*H+H*Dᵀ) (A z) v := by
    simp only [tensorMetricTrace,Matrix.neg_apply,neg_mul,Finset.sum_neg_distrib]
  rw [hneg] at hd
  rw [covariantD_cons]
  change rDeriv (fun w => tensorMetricTrace (realMetricFn h c w)⁻¹ (A w) v) z i-
    tensorConnectionAction D (tensorMetricTrace H (A z)) v=
      tensorMetricTrace H (fun u => covariantD h c A z (Fin.cons i u)) v
  simp_rw [covariantD_cons]
  rw [tensorMetricTrace_sub,tensorMetricTrace_connectionAction]
  change rDeriv (fun w => tensorMetricTrace (realMetricFn h c w)⁻¹ (A w) v) z i-
    tensorConnectionAction D (tensorMetricTrace H (A z)) v=
      tensorMetricTrace H (fun u => rDeriv (fun w => A w u) z i) v-
        (tensorMetricTrace (D*H+H*Dᵀ) (A z) v+
          tensorConnectionAction D (tensorMetricTrace H (A z)) v)
  linarith [hd]

end Yau.LeafProofs.L23Aux
