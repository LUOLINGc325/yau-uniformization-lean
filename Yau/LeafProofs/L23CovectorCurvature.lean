import Yau.LeafProofs.L23TensorChart
import Yau.LeafProofs.L23RicciBound

/-! Curvature of the original connection recovered from covector commutators. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def tensorAltFirstTwo (T : RealTensorForm n 3) : RealTensorForm n 3 :=
  T-ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 3) 1) T

theorem tensorAltFirstTwo_apply (T : RealTensorForm n 3) (V : Fin 3 → ComplexVector n) :
    tensorAltFirstTwo T V=T V-T (fun j => V (Equiv.swap (0 : Fin 3) 1 j)) := by
  simp only [tensorAltFirstTwo,sub_apply,ContinuousMultilinearMap.domDomCongr_apply]

theorem tensorAltFirstTwo_three (T : RealTensorForm n 3) (u v w : ComplexVector n) :
    tensorAltFirstTwo T ![u,v,w]=T ![u,v,w]-T ![v,u,w] := by
  rw [tensorAltFirstTwo_apply]
  congr 1
  apply congrArg T
  funext j
  fin_cases j <;> simp [Equiv.swap_apply_def]

theorem tensorAltFirstTwo_coefficients (A : CovTensor n 3) :
    tensorAltFirstTwo (tensorEvalCLM A)=
      tensorEvalCLM (fun v => A v-A (fun j => v (Equiv.swap (0 : Fin 3) 1 j))) := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin 3 => L12Aux.realVec_basis n)
  intro v
  change tensorAltFirstTwo (tensorEvalCLM A) (fun j => L12Aux.realVec_basis n (v j))=_
  simp only [L12Aux.realVec_basis_apply,tensorAltFirstTwo_apply]
  change tensorEvalCLM A (fun j => realVec (v j))-
      tensorEvalCLM A (fun j => realVec (v (Equiv.swap (0 : Fin 3) 1 j)))=
    tensorEvalCLM (fun v => A v-A (fun j => v (Equiv.swap (0 : Fin 3) 1 j)))
      (fun j => realVec (v j))
  rw [tensorEvalCLM_basis,tensorEvalCLM_basis,tensorEvalCLM_basis]

theorem tensorAltFirstTwo_comp (T : RealTensorForm n 3)
    (J : ComplexVector n →L[ℝ] ComplexVector n) :
    tensorAltFirstTwo (T.compContinuousLinearMap (fun _ : Fin 3 => J))=
      (tensorAltFirstTwo T).compContinuousLinearMap (fun _ : Fin 3 => J) := by
  ext V
  simp only [tensorAltFirstTwo_apply,ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem tensorEvalCLM_three (A : CovTensor n 3) (u v w : ComplexVector n) :
    tensorEvalCLM A ![u,v,w]=∑ i, ∑ j, ∑ k,
      A ![i,j,k]*realCoord u i*realCoord v j*realCoord w k := by
  simp [tensorEvalCLM_apply,sum_tensor_cons,Fin.prod_univ_succ,mul_assoc]
  rfl

variable {M : ComplexManifold n}

theorem covector_curvature_alt_form (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n 1)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hA : ∀ v, ContDiffAt ℝ 2 (fun w => A w v) z) :
    tensorAltFirstTwo (tensorEvalCLM (covariantD h c (covariantD h c A) z))=
      tensorEvalCLM (fun v : Fin 3 → RIdx n =>
        -∑ b, riemannCoeff h c z (v 0) (v 1) (v 2) b*A z ![b]) := by
  rw [tensorAltFirstTwo_coefficients]
  congr 1
  funext v
  let i := v 0
  let j := v 1
  let k := v 2
  have hv : v=![i,j,k] := by funext a; fin_cases a <;> rfl
  have hswap : (fun a : Fin 3 => ![i,j,k] (Equiv.swap (0 : Fin 3) 1 a))=![j,i,k] := by
    funext a
    fin_cases a <;> simp [Equiv.swap_apply_def]
  rw [hv,hswap]
  change covariantD h c (covariantD h c A) z ![i,j,k]-
    covariantD h c (covariantD h c A) z ![j,i,k]=
      -∑ b, riemannCoeff h c z i j k b*A z ![b]
  have hc := covariantD_commutator_at h hh c A hz hA i j ![k]
  have hupdate (b : RIdx n) : Function.update ![k] (0 : Fin 1) b=![b] := by
    funext a
    have ha : a=0 := Subsingleton.elim _ _
    subst a
    simp only [Function.update_self]
    rfl
  simpa [Fin.sum_univ_succ,hupdate] using hc

end Yau.LeafProofs.L23Aux
