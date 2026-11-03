import Yau.LeafProofs.L23ConnectionTensorLowering

/-! Full covariant derivative of the actual lowered curvature, including
the connection terms on both curvature-input slots. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
open L18Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def lowerCurvatureTensor (h : HermitianField M) (c : M.Carrier)
    (C : ComplexVector n → RIdx n → RIdx n → RIdx n → RIdx n → ℝ)
    (z : ComplexVector n) : CovTensor n 4 :=
  fun v => ∑ p, realMetricFn h c z p (v 3)*C z p (v 0) (v 1) (v 2)

theorem covariantD_lowerCurvatureTensor_expand (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (C : ComplexVector n → RIdx n → RIdx n → RIdx n → RIdx n → ℝ)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hC : ∀ p i j k, DifferentiableAt ℝ (fun w => C w p i j k) z) (a i j k l : RIdx n) :
    covariantD h c (lowerCurvatureTensor h c C) z ![a,i,j,k,l]=
      ∑ p, realMetricFn h c z p l*
        (rDeriv (fun w => C w p i j k) z a+
          (∑ q, christoffel h c z p a q*C z q i j k)-
            (∑ q, christoffel h c z q a i*C z p q j k)-
              (∑ q, christoffel h c z q a j*C z p i q k)-
                ∑ q, christoffel h c z q a k*C z p i j q) := by
  have hG (p q : RIdx n) := ((hh c p q).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hD : rDeriv (fun w => ∑ p, realMetricFn h c w p l*C w p i j k) z a=
      ∑ p, (rDeriv (fun w => realMetricFn h c w p l) z a*C z p i j k+
        realMetricFn h c z p l*rDeriv (fun w => C w p i j k) z a) := by
    calc
      _=∑ p, rDeriv (fun w => realMetricFn h c w p l*C w p i j k) z a :=
        rDeriv_sum (fun p w => realMetricFn h c w p l*C w p i j k)
          (fun p => (hG p l).mul (hC p i j k)) a
      _=_ := by
        apply Finset.sum_congr rfl
        intro p _
        exact rDeriv_mul (hG p l) (hC p i j k) a
  simp [covariantD,lowerCurvatureTensor,Fin.sum_univ_succ]
  change rDeriv (fun w => ∑ p, realMetricFn h c w p l*C w p i j k) z a-
    ((∑ q, christoffel h c z q a i*∑ p, realMetricFn h c z p l*C z p q j k)+
      ((∑ q, christoffel h c z q a j*∑ p, realMetricFn h c z p l*C z p i q k)+
        ((∑ q, christoffel h c z q a k*∑ p, realMetricFn h c z p l*C z p i j q)+
          (∑ q, christoffel h c z q a l*∑ p, realMetricFn h c z p q*C z p i j k))))=_
  rw [hD]
  simp_rw [metric_rDeriv_connection h hh c hz]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_mul,
    Finset.mul_sum,mul_add,mul_sub,add_mul]
  have hswap (f : RIdx n → RIdx n → ℝ) : (∑ q, ∑ p, f q p)=(∑ p, ∑ q, f q p) :=
    Finset.sum_comm
  rw [hswap (fun q p => christoffel h c z q a i*(realMetricFn h c z p l*C z p q j k)),
    hswap (fun q p => christoffel h c z q a j*(realMetricFn h c z p l*C z p i q k)),
    hswap (fun q p => christoffel h c z q a k*(realMetricFn h c z p l*C z p i j q)),
    hswap (fun q p => christoffel h c z q a l*(realMetricFn h c z p q*C z p i j k))]
  have hmetric : (∑ p, ∑ q, christoffel h c z q a p*realMetricFn h c z q l*C z p i j k)=
      ∑ p, ∑ q, realMetricFn h c z p l*(christoffel h c z p a q*C z q i j k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hmetric]
  simp only [mul_comm,mul_left_comm,mul_assoc]
  ring

theorem covariantD_rmTensor_five (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a i j k l : RIdx n) :
    covariantD h c (rmTensor h c) z ![a,i,j,k,l]=
      ∑ p, realMetricFn h c z p l*
        (rDeriv (fun w => riemannCoeff h c w i j k p) z a+
          (∑ q, christoffel h c z p a q*riemannCoeff h c z i j k q)-
            (∑ q, christoffel h c z q a i*riemannCoeff h c z q j k p)-
              (∑ q, christoffel h c z q a j*riemannCoeff h c z i q k p)-
                ∑ q, christoffel h c z q a k*riemannCoeff h c z i j q p) := by
  have hC (p i j k : RIdx n) := ((riemannCoeff_contDiffOn h hh c i j k p).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  exact covariantD_lowerCurvatureTensor_expand h hh c
    (fun w p i j k => riemannCoeff h c w i j k p) hz hC a i j k l

end Yau.LeafProofs.L23Aux
