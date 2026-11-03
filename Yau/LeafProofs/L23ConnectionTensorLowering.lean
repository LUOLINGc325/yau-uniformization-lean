import Yau.LeafProofs.L23TensorNormCalculus

/-! Lowering an upper connection-variation slot commutes with the actual
metric-compatible covariant derivative. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
open L18Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def lowerConnectionTensor (h : HermitianField M) (c : M.Carrier)
    (C : ComplexVector n → RIdx n → RIdx n → RIdx n → ℝ)
    (z : ComplexVector n) : CovTensor n 3 :=
  fun v => ∑ p, realMetricFn h c z p (v 2)*C z p (v 0) (v 1)

theorem metric_rDeriv_connection (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (i p l : RIdx n) :
    rDeriv (fun w => realMetricFn h c w p l) z i=
      (∑ a, christoffel h c z a i p*realMetricFn h c z a l)+
        ∑ a, realMetricFn h c z p a*christoffel h c z a i l := by
  have heq := congrArg (fun B : Matrix (RIdx n) (RIdx n) ℝ => B p l)
    (metricDirectionalDerivative_eq_connection h hh c z hz i)
  exact heq

theorem covariantD_lowerConnectionTensor_expand (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (C : ComplexVector n → RIdx n → RIdx n → RIdx n → ℝ)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hC : ∀ p j k, DifferentiableAt ℝ (fun w => C w p j k) z) (i j k l : RIdx n) :
    covariantD h c (lowerConnectionTensor h c C) z ![i,j,k,l]=
      ∑ p, realMetricFn h c z p l*
        (rDeriv (fun w => C w p j k) z i+
          (∑ a, christoffel h c z p i a*C z a j k)-
            (∑ a, christoffel h c z a i j*C z p a k)-
              ∑ a, christoffel h c z a i k*C z p j a) := by
  have hG (p q : RIdx n) := ((hh c p q).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hD : rDeriv (fun w => ∑ p, realMetricFn h c w p l*C w p j k) z i=
      ∑ p, (rDeriv (fun w => realMetricFn h c w p l) z i*C z p j k+
        realMetricFn h c z p l*rDeriv (fun w => C w p j k) z i) := by
    calc
      _=∑ p, rDeriv (fun w => realMetricFn h c w p l*C w p j k) z i :=
        rDeriv_sum (fun p w => realMetricFn h c w p l*C w p j k)
          (fun p => (hG p l).mul (hC p j k)) i
      _=_ := by
        apply Finset.sum_congr rfl
        intro p _
        exact rDeriv_mul (hG p l) (hC p j k) i
  simp [covariantD,lowerConnectionTensor,Fin.sum_univ_succ]
  change rDeriv (fun w => ∑ p, realMetricFn h c w p l*C w p j k) z i-
    ((∑ a, christoffel h c z a i j*∑ p, realMetricFn h c z p l*C z p a k)+
      ((∑ a, christoffel h c z a i k*∑ p, realMetricFn h c z p l*C z p j a)+
        (∑ a, christoffel h c z a i l*∑ p, realMetricFn h c z p a*C z p j k)))=_
  rw [hD]
  simp_rw [metric_rDeriv_connection h hh c hz]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_mul,
    Finset.mul_sum,mul_add,mul_sub,add_mul]
  have hswap (f : RIdx n → RIdx n → ℝ) : (∑ a, ∑ p, f a p)=(∑ p, ∑ a, f a p) :=
    Finset.sum_comm
  rw [hswap (fun a p => christoffel h c z a i j*(realMetricFn h c z p l*C z p a k)),
    hswap (fun a p => christoffel h c z a i k*(realMetricFn h c z p l*C z p j a)),
    hswap (fun a p => christoffel h c z a i l*(realMetricFn h c z p a*C z p j k))]
  have hmetric : (∑ p, ∑ a, christoffel h c z a i p*realMetricFn h c z a l*C z p j k)=
      ∑ p, ∑ a, realMetricFn h c z p l*(christoffel h c z p i a*C z a j k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hmetric]
  simp only [mul_comm,mul_left_comm,mul_assoc]
  ring

theorem covariantD_lowerConnectionTensor_curl (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (C : ComplexVector n → RIdx n → RIdx n → RIdx n → ℝ)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hC : ∀ p j k, DifferentiableAt ℝ (fun w => C w p j k) z) (i j k l : RIdx n) :
    covariantD h c (lowerConnectionTensor h c C) z ![i,j,k,l]-
      covariantD h c (lowerConnectionTensor h c C) z ![j,i,k,l]=
      ∑ p, realMetricFn h c z p l*
        (rDeriv (fun w => C w p j k) z i-rDeriv (fun w => C w p i k) z j+
          ∑ a, ((C z a j k*christoffel h c z p i a+
            christoffel h c z a j k*C z p i a)-
              (C z a i k*christoffel h c z p j a+
                christoffel h c z a i k*C z p j a))) := by
  rw [covariantD_lowerConnectionTensor_expand h hh c C hz hC,
    covariantD_lowerConnectionTensor_expand h hh c C hz hC]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [←mul_sub]
  congr 1
  have hΓ : (∑ a, christoffel h c z a j i*C z p a k)=
      ∑ a, christoffel h c z a i j*C z p a k := by
    simp only [L12Aux.christoffel_symm_lower h c z (a := j) (b := i)]
  rw [hΓ]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp only [mul_comm,mul_left_comm,mul_assoc]
  ring

end Yau.LeafProofs.L23Aux
