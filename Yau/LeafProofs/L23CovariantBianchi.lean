import Yau.LeafProofs.L23CurvatureDerivative

/-! The full second Bianchi identity for the original fully lowered Rm. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem covariantD_rmTensor_secondBianchi (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a i j k l : RIdx n) :
    covariantD h c (rmTensor h c) z ![a,i,j,k,l]+
      covariantD h c (rmTensor h c) z ![i,j,a,k,l]+
        covariantD h c (rmTensor h c) z ![j,a,i,k,l]=0 := by
  rw [covariantD_rmTensor_five h hh c hz,covariantD_rmTensor_five h hh c hz,
    covariantD_rmTensor_five h hh c hz,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro p _
  have hm := congrArg (fun B : Matrix (RIdx n) (RIdx n) ℝ => B p k)
    (curvatureMatrix_secondBianchi h hh c hz a i j)
  change
    (rDeriv (fun w => riemannCoeff h c w i j k p) z a+
      (∑ q, christoffel h c z p a q*riemannCoeff h c z i j k q)-
        ∑ q, riemannCoeff h c z i j q p*christoffel h c z q a k)+
    (rDeriv (fun w => riemannCoeff h c w j a k p) z i+
      (∑ q, christoffel h c z p i q*riemannCoeff h c z j a k q)-
        ∑ q, riemannCoeff h c z j a q p*christoffel h c z q i k)+
    (rDeriv (fun w => riemannCoeff h c w a i k p) z j+
      (∑ q, christoffel h c z p j q*riemannCoeff h c z a i k q)-
        ∑ q, riemannCoeff h c z a i q p*christoffel h c z q j k)=0 at hm
  have hpair (a i j : RIdx n) :
      (∑ q, christoffel h c z q a i*riemannCoeff h c z q j k p)+
        (∑ q, christoffel h c z q i a*riemannCoeff h c z j q k p)=0 := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro q _
    rw [L12Aux.christoffel_symm_lower h c z (a := i) (b := a),
      L12Aux.riemannCoeff_swap h c z q j k p]
    ring
  have h1 := hpair a i j
  have h2 := hpair j a i
  have h3 := hpair i j a
  rw [←mul_add,←mul_add]
  apply mul_eq_zero_of_right
  simp only [mul_comm,mul_left_comm,mul_assoc] at hm h1 h2 h3 ⊢
  linarith [hm,h1,h2,h3]

end Yau.LeafProofs.L23Aux
