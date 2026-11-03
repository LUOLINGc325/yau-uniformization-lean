import Yau.LeafProofs.L23CommutatorAt
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! The actual finite tensor coefficients as continuous multilinear forms. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ}

abbrev RealTensorForm (n r : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin r => ComplexVector n) ℝ

def tensorMonomial (v : Fin r → RIdx n) : RealTensorForm n r :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
    (fun j => L12Aux.realCoordCLM (v j))

def tensorEvalCLMMap : CovTensor n r →L[ℝ] RealTensorForm n r :=
  ∑ v : Fin r → RIdx n, (ContinuousLinearMap.proj v).smulRight (tensorMonomial v)

def tensorEvalCLM (A : CovTensor n r) : RealTensorForm n r := tensorEvalCLMMap A

theorem tensorEvalCLM_apply (A : CovTensor n r) (V : Fin r → ComplexVector n) :
    tensorEvalCLM A V=∑ v : Fin r → RIdx n, A v*∏ j : Fin r, realCoord (V j) (v j) := by
  simp [tensorEvalCLM,tensorEvalCLMMap,tensorMonomial,L12Aux.realCoordCLM_apply]

theorem tensorEvalCLM_basis (A : CovTensor n r) (v : Fin r → RIdx n) :
    tensorEvalCLM A (fun j => realVec (v j))=A v := by
  classical
  rw [tensorEvalCLM_apply,Finset.sum_eq_single v]
  · simp [L12Aux.realCoord_realVec]
  · intro w _ hw
    have hex : ∃ j : Fin r, w j ≠ v j := by
      by_contra hnot
      apply hw
      funext j
      by_contra hj
      exact hnot ⟨j,hj⟩
    obtain ⟨j,hj⟩ := hex
    have hp : (∏ k : Fin r, realCoord (realVec (v k)) (w k))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [L12Aux.realCoord_realVec,Ne.symm hj]
    rw [hp,mul_zero]
  · simp

theorem tensorEvalCLM_injective : Function.Injective (tensorEvalCLM (n := n) (r := r)) := by
  intro A B hAB
  funext v
  have hh := congrArg (fun T : RealTensorForm n r => T (fun j => realVec (v j))) hAB
  simpa only [tensorEvalCLM_basis] using hh

theorem tensorEvalCLM_coefficients (T : RealTensorForm n r) :
    tensorEvalCLM (fun v => T (fun j => realVec (v j)))=T := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin r => L12Aux.realVec_basis n)
  intro v
  change tensorEvalCLM (fun v => T (fun j => realVec (v j)))
    (fun i => L12Aux.realVec_basis n (v i))=T (fun i => L12Aux.realVec_basis n (v i))
  simpa only [L12Aux.realVec_basis_apply] using
    tensorEvalCLM_basis (fun v => T (fun j => realVec (v j))) v

theorem tensorEvalCLM_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → CovTensor n r) {O : Set E}
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) O) :
    ContDiffOn ℝ ∞ (fun z => tensorEvalCLM (A z)) O :=
  tensorEvalCLMMap.contDiff.comp_contDiffOn (contDiffOn_pi.mpr hA)

theorem tensorEvalCLM_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → CovTensor n r) {z : E} (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z) (u : E) :
    fderiv ℝ (fun w => tensorEvalCLM (A w)) z u =
      tensorEvalCLM (fun v => fderiv ℝ (fun w => A w v) z u) := by
  have hdA : HasFDerivAt A (ContinuousLinearMap.pi (fun v => fderiv ℝ (fun w => A w v) z)) z :=
    hasFDerivAt_pi.mpr (fun v => (hA v).hasFDerivAt)
  have hd := tensorEvalCLMMap.hasFDerivAt.comp z hdA
  have hh := congrArg (fun L : E →L[ℝ] RealTensorForm n r => L u) hd.fderiv
  change fderiv ℝ (fun w => tensorEvalCLM (A w)) z u =
    tensorEvalCLM (fun v => fderiv ℝ (fun w => A w v) z u) at hh
  exact hh

theorem tensorEvalCLM_head_basis (A : CovTensor n (r+1)) (u : ComplexVector n)
    (v : Fin r → RIdx n) :
    tensorEvalCLM A (Fin.cons u (fun j => realVec (v j))) =
      ∑ a : RIdx n, realCoord u a*A (Fin.cons a v) := by
  have hcoef (a : RIdx n) : tensorEvalCLM A (Fin.cons (realVec a) (fun j => realVec (v j)))=
      A (Fin.cons a v) := by
    have hvec : Fin.cons (realVec a) (fun j => realVec (v j))=
        (fun j : Fin (r+1) => realVec ((Fin.cons a v : Fin (r+1) → RIdx n) j)) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> rfl
    rw [hvec,tensorEvalCLM_basis]
  change ((tensorEvalCLM A).curryLeft u) (fun j => realVec (v j))=_
  conv_lhs => rw [←L12Aux.sum_realCoord_realVec u]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,
    ContinuousMultilinearMap.curryLeft_apply,hcoef]

theorem tensorEvalCLM_update_basis (A : CovTensor n r) (u : ComplexVector n)
    (v : Fin r → RIdx n) (s : Fin r) :
    tensorEvalCLM A (Function.update (fun j => realVec (v j)) s u) =
      ∑ b : RIdx n, realCoord u b*A (Function.update v s b) := by
  let L := (tensorEvalCLM A).toContinuousLinearMap (fun j => realVec (v j)) s
  change L u=_
  conv_lhs => rw [←L12Aux.sum_realCoord_realVec u]
  simp only [map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  change tensorEvalCLM A (Function.update (fun j => realVec (v j)) s (realVec b))=_
  have hvec : Function.update (fun j => realVec (v j)) s (realVec b)=
      (fun j => realVec (Function.update v s b j)) := by
    funext j
    by_cases hjs : j=s
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hjs]
  rw [hvec,tensorEvalCLM_basis]

def tensorConnectionForm (Γ : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (A : RealTensorForm n r) (u : ComplexVector n) : RealTensorForm n r :=
  ∑ s : Fin r, A.compContinuousLinearMap
    (fun j => if j=s then Γ u else ContinuousLinearMap.id ℝ (ComplexVector n))

theorem tensorConnectionForm_apply (Γ : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (A : RealTensorForm n r) (u : ComplexVector n) (V : Fin r → ComplexVector n) :
    tensorConnectionForm Γ A u V=∑ s : Fin r, A (Function.update V s (Γ u (V s))) := by
  simp only [tensorConnectionForm,sum_apply,ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  funext j
  by_cases hjs : j=s
  · subst j
    simp only [ite_eq_left,Function.update_self]
  · simp only [ite_eq_right hjs,ContinuousLinearMap.id_apply,Function.update_of_ne hjs]

variable {M : ComplexManifold n}

theorem chartChristoffelBilin_realCoord_basis (h : HermitianField M) (c : M.Carrier)
    (z u : ComplexVector n) (j b : RIdx n) :
    realCoord (L12Aux.chartChristoffelBilin h c z u (realVec j)) b =
      ∑ a : RIdx n, realCoord u a*christoffel h c z b a j := by
  rw [L12Aux.chartChristoffelBilin_apply,L12Aux.realCoord_sum_realVec]
  simp [L12Aux.realCoord_realVec,mul_comm,mul_left_comm,mul_assoc]

/-- Multilinear evaluation of the original covariant derivative, with the
new derivative slot first. No extra connection has been introduced. -/
theorem tensorEvalCLM_covariantD (h : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (z u : ComplexVector n)
    (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z) :
    (tensorEvalCLM (covariantD h c A z)).curryLeft u =
      fderiv ℝ (fun w => tensorEvalCLM (A w)) z u-
        tensorConnectionForm (L12Aux.chartChristoffelBilin h c z) (tensorEvalCLM (A z)) u := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin r => L12Aux.realVec_basis n)
  intro v
  change tensorEvalCLM (covariantD h c A z)
    (Fin.cons u (fun j => L12Aux.realVec_basis n (v j))) =
    (fderiv ℝ (fun w => tensorEvalCLM (A w)) z u) (fun j => L12Aux.realVec_basis n (v j))-
      tensorConnectionForm (L12Aux.chartChristoffelBilin h c z) (tensorEvalCLM (A z)) u
        (fun j => L12Aux.realVec_basis n (v j))
  simp only [L12Aux.realVec_basis_apply]
  rw [tensorEvalCLM_head_basis,tensorEvalCLM_fderiv A hA u,tensorEvalCLM_basis,
    tensorConnectionForm_apply]
  simp_rw [tensorEvalCLM_update_basis,chartChristoffelBilin_realCoord_basis]
  have hdu : fderiv ℝ (fun w => A w v) z u =
      ∑ a : RIdx n, realCoord u a*rDeriv (fun w => A w v) z a := by
    conv_lhs => rw [←L12Aux.sum_realCoord_realVec u]
    simp only [map_sum,map_smul,smul_eq_mul,rDeriv]
  rw [hdu]
  simp only [covariantD_cons,tensorConnectionAction,tensorSlotAction,L12Aux.connectionMatrix,
    mul_sub,Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_mul,mul_assoc]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]

end Yau.LeafProofs.L23Aux
