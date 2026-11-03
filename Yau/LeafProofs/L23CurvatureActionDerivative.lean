import Yau.LeafProofs.L23RoughLapCommutator
import Yau.LeafProofs.L23TensorActionCalculus
import Yau.LeafProofs.L23UpperCurvatureDerivative

/-! The derivative of the full curvature action, with the two curvature
input slots differentiated as genuine covariant slots. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
open L18Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {M : ComplexManifold n}

theorem curvatureAction_eq_neg_tensorConnectionAction (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (i j : RIdx n) (A : CovTensor n r) (v : Fin r → RIdx n) :
    curvatureAction h c z i j A v=
      -tensorConnectionAction (L12Aux.curvatureMatrix h c z i j) A v := rfl

theorem curvatureActionField_cons (h : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (z : ComplexVector n)
    (i j : RIdx n) (v : Fin r → RIdx n) :
    curvatureActionField h c A z (Fin.cons i (Fin.cons j v))=
      curvatureAction h c z i j (A z) v := rfl

theorem covariantD_curvatureActionField_raw (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun w => A w v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (a i b : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c (curvatureActionField h c A) z (Fin.cons a (Fin.cons i (Fin.cons b v)))=
      -tensorConnectionAction
        (L12Aux.matrixDirectionalDerivative (fun w => L12Aux.curvatureMatrix h c w i b) z (realVec a)) (A z) v-
      tensorConnectionAction (L12Aux.curvatureMatrix h c z i b)
        (fun u => rDeriv (fun w => A w u) z a) v+
      (∑ p, christoffel h c z p a i*
        tensorConnectionAction (L12Aux.curvatureMatrix h c z p b) (A z) v)+
      (∑ p, christoffel h c z p a b*
        tensorConnectionAction (L12Aux.curvatureMatrix h c z i p) (A z) v)+
      tensorConnectionAction (L12Aux.connectionMatrix h c z a)
        (tensorConnectionAction (L12Aux.curvatureMatrix h c z i b) (A z)) v := by
  have hAd (u : Fin r → RIdx n) := ((hA u).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hRd (p q : RIdx n) := ((riemannCoeff_contDiffOn h hh c i b q p).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hd := tensorConnectionAction_rDeriv (fun w => L12Aux.curvatureMatrix h c w i b)
    A z hRd hAd a v
  have hneg : rDeriv (fun w => curvatureAction h c w i b (A w) v) z a=
      -tensorConnectionAction
        (L12Aux.matrixDirectionalDerivative (fun w => L12Aux.curvatureMatrix h c w i b) z (realVec a)) (A z) v-
      tensorConnectionAction (L12Aux.curvatureMatrix h c z i b)
        (fun u => rDeriv (fun w => A w u) z a) v := by
    simp_rw [curvatureAction_eq_neg_tensorConnectionAction]
    have hn : rDeriv (fun w => -tensorConnectionAction (L12Aux.curvatureMatrix h c w i b) (A w) v) z a=
        -rDeriv (fun w => tensorConnectionAction (L12Aux.curvatureMatrix h c w i b) (A w) v) z a := by
      unfold rDeriv
      rw [fderiv_fun_neg]
      rfl
    have hdot : (fun p q => rDeriv (fun w => L12Aux.curvatureMatrix h c w i b p q) z a)=
        L12Aux.matrixDirectionalDerivative (fun w => L12Aux.curvatureMatrix h c w i b) z (realVec a) := rfl
    rw [hn,hd,hdot]
    ring
  rw [covariantD_cons,tensorConnectionAction_cons,tensorConnectionAction_cons]
  simp only [curvatureActionField_cons]
  rw [hneg]
  simp only [curvatureAction_eq_neg_tensorConnectionAction,L12Aux.connectionMatrix,mul_neg,Finset.sum_neg_distrib,
    tensorConnectionAction_neg_tensor]
  ring

theorem covariantD_curvatureActionField_upperDerivative
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun w => A w v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (a i b : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c (curvatureActionField h c A) z (Fin.cons a (Fin.cons i (Fin.cons b v)))=
      -tensorConnectionAction (upperCurvatureDerivativeMatrix h c z a i b) (A z) v-
        tensorConnectionAction (L12Aux.curvatureMatrix h c z i b)
          (fun u => covariantD h c A z (Fin.cons a u)) v := by
  rw [covariantD_curvatureActionField_raw h hh c A hA hz,
    upperCurvatureDerivative_matrix]
  simp_rw [tensorConnectionAction_sub_matrix,tensorConnectionAction_add_matrix,
    tensorConnectionAction_sum_matrix,tensorConnectionAction_smul_matrix,covariantD_cons]
  rw [tensorConnectionAction_sub_tensor]
  have hc := tensorConnectionAction_commutator (L12Aux.connectionMatrix h c z a)
    (L12Aux.curvatureMatrix h c z i b) (A z) v
  rw [tensorConnectionAction_sub_matrix] at hc
  linarith [hc]

end Yau.LeafProofs.L23Aux
