import Yau.LeafProofs.L21WeightedDomainsJointCore

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem weightedSSystemApply_eq_degenerateS
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (u : X n → Fin n → ℂ)
    (x : X n) (r : Fin n × Fin n) :
    Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply Yau.realVec (weightedSPrincipal A)
      (weightedSZeroOrder A) u x r = degenerateS A u x r.1 r.2 := by
  simp only [Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply,weightedSPrincipal,weightedSZeroOrder,
    degenerateS,scaledGraphCurl,dbarA_eq_real_rows,mul_sub,sub_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp_rw [mul_ite,ite_mul,zero_mul,mul_zero,Finset.sum_ite_irrel]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_assoc,← Finset.mul_sum,zero_mul,Finset.sum_const_zero]
  ring

theorem weightedDomains_conjugateD_mul
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (j : Fin n)
    {f g : X n → ℂ} {x : X n} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    conjugateD A j (fun y => f y*g y) x = conjugateD A j f x*g x+f x*conjugateD A j g x := by
  simp only [conjugateD,fderiv_fun_mul hf hg,_root_.add_apply,_root_.smul_apply,smul_eq_mul,
    mul_add,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

theorem weightedTstarSystemApply_eq_formalTstar
    (K : ℝ) (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (u : X n → Fin n → ℂ) (x : X n)
    (hu : ∀ j, DifferentiableAt ℝ (fun y => u y j) x) :
    Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply Yau.realVec (weightedTstarPrincipal A)
      (weightedTstarZeroOrder K A) u x () =
      ∑ j, weightedDStar A (boundaryWeight K) j (fun y => (rho y : ℂ)*u y j) x := by
  apply Finset.sum_congr rfl
  intro j hj
  have hrho : DifferentiableAt ℝ (fun y : X n => (rho y : ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp contDiff_rho).differentiable (by simp) x
  rw [weightedDStar,weightedDomains_conjugateD_mul A j hrho (hu j)]
  change (∑ a, (-(rho x : ℂ)*star (dbarRealCoefficient A j a x))*
      fderiv ℝ (fun y => u y j) x (Yau.realVec a))+
      ((rho x : ℂ)*(conjugateD A j (fun y => (boundaryWeight K y : ℂ)) x-conjugateDivergence A j x)-
        conjugateD A j (fun y => (rho y : ℂ)) x)*u x j = _
  simp only [conjugateD,neg_mul,mul_assoc,Finset.sum_neg_distrib,← Finset.mul_sum]
  ring

end Yau.LeafProofs.L21Aux
