import Yau.LeafProofs.L23CurvatureActionDerivative

/-! The exact three families in the full-rank spatial commutator. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {M : ComplexManifold n}

theorem curvatureAction_cons (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (i a b : RIdx n) (B : CovTensor n (r+1)) (v : Fin r → RIdx n) :
    curvatureAction h c z i a B (Fin.cons b v)=
      -(∑ p, riemannCoeff h c z i a b p*B (Fin.cons p v))+
        curvatureAction h c z i a (fun u => B (Fin.cons b u)) v := by
  rw [curvatureAction_eq_neg_tensorConnectionAction,tensorConnectionAction_cons,
    curvatureAction_eq_neg_tensorConnectionAction]
  change -((∑ p, riemannCoeff h c z i a b p*B (Fin.cons p v))+
    tensorConnectionAction (L12Aux.curvatureMatrix h c z i a) (fun u => B (Fin.cons b u)) v)=_
  ring

theorem covariantD_roughLap_commutator_upper (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun w => A w v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (i : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c (roughLap h c A) z (Fin.cons i v)-
      roughLap h c (covariantD h c A) z (Fin.cons i v)=
      -(∑ a, ∑ b, ∑ p, (realMetricFn h c z)⁻¹ a b*riemannCoeff h c z i a b p*
        covariantD h c A z (Fin.cons p v))-
      2*(∑ a, ∑ b, ∑ s : Fin r, ∑ p,
        (realMetricFn h c z)⁻¹ a b*riemannCoeff h c z i a (v s) p*
          covariantD h c A z (Fin.cons b (Function.update v s p)))-
      (∑ a, ∑ b, ∑ s : Fin r, ∑ p,
        (realMetricFn h c z)⁻¹ a b*upperCurvatureDerivativeMatrix h c z a i b p (v s)*
          A z (Function.update v s p)) := by
  have hw := covariantD_roughLap_commutator_raw h hh c A hA hz i v
  simp_rw [curvatureAction_cons,covariantD_curvatureActionField_upperDerivative h hh c A hA hz] at hw
  simp only [curvatureAction,tensorConnectionAction,tensorSlotAction,L12Aux.curvatureMatrix,
    mul_add,mul_sub,mul_neg,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.sum_neg_distrib,Finset.mul_sum] at hw
  have hswap : (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
      (∑ s : Fin r, ∑ p, riemannCoeff h c z i b (v s) p*
        covariantD h c A z (Fin.cons a (Function.update v s p))))=
      ∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
        (∑ s : Fin r, ∑ p, riemannCoeff h c z i a (v s) p*
          covariantD h c A z (Fin.cons b (Function.update v s p))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [(L18Aux.realMetricFn_isSymm h c z).inv.apply b a]
  simp only [Finset.mul_sum] at hswap
  simp only [mul_comm,mul_left_comm,mul_assoc] at hw hswap ⊢
  linarith [hw,hswap]

end Yau.LeafProofs.L23Aux
