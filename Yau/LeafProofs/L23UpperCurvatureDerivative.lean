import Yau.LeafProofs.L23CurvatureEvolution

/-! Raising the final slot of the original Rm covariant derivative. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def upperCurvatureDerivativeMatrix (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (a i j : RIdx n) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun p k => rDeriv (fun w => riemannCoeff h c w i j k p) z a+
    (∑ q, christoffel h c z p a q*riemannCoeff h c z i j k q)-
      (∑ q, christoffel h c z q a i*riemannCoeff h c z q j k p)-
        (∑ q, christoffel h c z q a j*riemannCoeff h c z i q k p)-
          ∑ q, christoffel h c z q a k*riemannCoeff h c z i j q p

theorem covariantD_rmTensor_upperDerivative (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a i j k l : RIdx n) :
    covariantD h c (rmTensor h c) z ![a,i,j,k,l]=
      ∑ p, realMetricFn h c z p l*upperCurvatureDerivativeMatrix h c z a i j p k :=
  covariantD_rmTensor_five h hh c hz a i j k l

theorem upperCurvatureDerivative_raise (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a i j p k : RIdx n) :
    upperCurvatureDerivativeMatrix h c z a i j p k=
      ∑ q, (realMetricFn h c z)⁻¹ p q*covariantD h c (rmTensor h c) z ![a,i,j,k,q] := by
  let G := realMetricFn h c z
  let V : RIdx n → ℝ := fun p => upperCurvatureDerivativeMatrix h c z a i j p k
  have hsym : Gᵀ=G := L18Aux.realMetricFn_isSymm h c z
  have hInv : G⁻¹*G=1 := Matrix.nonsing_inv_mul G
    (isUnit_iff_ne_zero.mpr (L12Aux.realMetricFn_posDef h c z hz).det_pos.ne')
  have hf : (fun q => covariantD h c (rmTensor h c) z ![a,i,j,k,q])=Gᵀ*ᵥV := by
    funext q
    exact covariantD_rmTensor_upperDerivative h hh c hz a i j k q
  change V p=(G⁻¹*ᵥ(fun q => covariantD h c (rmTensor h c) z ![a,i,j,k,q])) p
  rw [hf,hsym,Matrix.mulVec_mulVec,hInv,Matrix.one_mulVec]

theorem upperCurvatureDerivative_matrix (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (a i j : RIdx n) :
    upperCurvatureDerivativeMatrix h c z a i j=
      L12Aux.matrixDirectionalDerivative (fun w => L12Aux.curvatureMatrix h c w i j) z (realVec a)+
        L12Aux.connectionMatrix h c z a*L12Aux.curvatureMatrix h c z i j-
          L12Aux.curvatureMatrix h c z i j*L12Aux.connectionMatrix h c z a-
            (∑ q, christoffel h c z q a i • L12Aux.curvatureMatrix h c z q j)-
              (∑ q, christoffel h c z q a j • L12Aux.curvatureMatrix h c z i q) := by
  ext p k
  simp only [upperCurvatureDerivativeMatrix,L12Aux.matrixDirectionalDerivative,
    L12Aux.connectionMatrix,L12Aux.curvatureMatrix,Matrix.add_apply,Matrix.sub_apply,
    Matrix.mul_apply,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul,rDeriv]
  simp only [mul_comm,mul_left_comm,mul_assoc]
  ring

end Yau.LeafProofs.L23Aux
