import Yau.LeafProofs.L21WeightedDomainsInner

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def weightedDualCompactTest (K : ℝ) (ξ : CompactTest (Metric.ball (0 : X n) 1)) :
    CompactTest (Metric.ball (0 : X n) 1) :=
  weightedLocalMultiplierTest (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (Real.contDiff_exp.comp_contDiffOn (contDiffOn_boundaryWeight K).neg)) (weightedConjugateTest ξ)

theorem weightedDualCompactTest_apply (K : ℝ) (ξ : CompactTest (Metric.ball (0 : X n) 1)) (x : X n) :
    weightedDualCompactTest K ξ x = weightDensity (boundaryWeight K) x*star (ξ x) := rfl

theorem weightedTstarTranspose_eq (K : ℝ)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (j : Fin n) (ψ : X n → ℂ) {x : X n} (hx : x ∈ Metric.ball 0 1) :
    weightedRowTranspose Yau.realVec (weightedTstarPrincipal A) (weightedTstarZeroOrder K A) () j ψ x =
      (rho x : ℂ)*(conjugateD A j ψ x+
        conjugateD A j (fun y => (boundaryWeight K y : ℂ)) x*ψ x) := by
  have hρ : DifferentiableAt ℝ (fun y : X n => (rho y : ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp contDiff_rho).differentiable (by simp) x
  have hp (a : Yau.RIdx n) : DifferentiableAt ℝ (fun y => star (dbarRealCoefficient A j a y)) x :=
    (((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (dbarRealCoefficient_smoothOn hA j a)).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
  have hDa (a : Yau.RIdx n) :
      fderiv ℝ (weightedTstarPrincipal A () j a) x (Yau.realVec a) =
        -fderiv ℝ (fun y => (rho y : ℂ)) x (Yau.realVec a)*star (dbarRealCoefficient A j a x)-
          (rho x : ℂ)*fderiv ℝ (fun y => star (dbarRealCoefficient A j a y)) x (Yau.realVec a) := by
    change fderiv ℝ (fun y => -(rho y : ℂ)*star (dbarRealCoefficient A j a y)) x (Yau.realVec a) = _
    have hρneg : DifferentiableAt ℝ (fun y : X n => -(rho y : ℂ)) x := hρ.neg
    rw [fderiv_fun_mul hρneg (hp a)]
    simp only [fderiv_fun_neg,_root_.add_apply,_root_.smul_apply,_root_.neg_apply,smul_eq_mul]
    ring
  simp only [weightedRowTranspose,hDa,weightedTstarPrincipal,weightedTstarZeroOrder,conjugateD,conjugateDivergence,
    add_mul,sub_mul,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    neg_mul,Finset.sum_neg_distrib,Finset.mul_sum,Finset.sum_mul]
  simp only [← Finset.sum_neg_distrib,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem weightedTstarTranspose_dualTest (K : ℝ)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (ξ : CompactTest (Metric.ball (0 : X n) 1)) (j : Fin n) (x : X n) :
    weightedRowTranspose Yau.realVec (weightedTstarPrincipal A) (weightedTstarZeroOrder K A)
      () j (weightedDualCompactTest K ξ) x =
      star (degenerateT A ξ x j)*weightDensity (boundaryWeight K) x := by
  by_cases hx : x ∈ Metric.ball (0 : X n) 1
  · have hφ := ((contDiffOn_boundaryWeight K).contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
    have hw : DifferentiableAt ℝ (weightDensity (boundaryWeight K)) x :=
      Complex.ofRealCLM.differentiableAt.comp x hφ.neg.exp
    have hξ := ξ.property.1.differentiable (by simp) x
    have hCancel (a : Yau.RIdx n) :
        fderiv ℝ (weightedDualCompactTest K ξ) x (Yau.realVec a)+
          fderiv ℝ (fun y => (boundaryWeight K y : ℂ)) x (Yau.realVec a)*weightedDualCompactTest K ξ x =
        weightDensity (boundaryWeight K) x*star (fderiv ℝ ξ x (Yau.realVec a)) := by
      change fderiv ℝ (fun y => weightDensity (boundaryWeight K) y*star (ξ y)) x (Yau.realVec a)+
        fderiv ℝ (fun y => (boundaryWeight K y : ℂ)) x (Yau.realVec a)*
          (weightDensity (boundaryWeight K) x*star (ξ x)) = _
      rw [fderiv_fun_mul hw hξ.star]
      simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul,
        fderiv_weightDensity hφ,fderiv_star_apply,fderiv_ofReal_apply hφ]
      ring
    rw [weightedTstarTranspose_eq K A hA j _ hx]
    simp only [conjugateD,Finset.sum_mul,← Finset.sum_add_distrib,← mul_add,hCancel]
    simp only [degenerateT,scaledGraphD,dbarA_eq_real_rows,star_mul,star_sum,
      show star (rho x : ℂ) = (rho x : ℂ) from Complex.conj_ofReal _,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    linear_combination (rho x : ℂ)*star (dbarRealCoefficient A j a x)*(hCancel a)
  · have hξ : x ∉ tsupport (ξ : X n → ℂ) := fun h => hx (ξ.property.2.2 h)
    have hψ : x ∉ tsupport (weightedDualCompactTest K ξ : X n → ℂ) :=
      fun h => hx ((weightedDualCompactTest K ξ).property.2.2 h)
    simp only [weightedRowTranspose,image_eq_zero_of_notMem_tsupport hψ,
      fderiv_of_notMem_tsupport ℝ hψ,ContinuousLinearMap.zero_apply,mul_zero,add_zero,
      Finset.sum_const_zero,neg_zero,degenerateT,scaledGraphD,dbarA_eq_real_rows,
      fderiv_of_notMem_tsupport ℝ hξ,star_zero,zero_mul]

end Yau.LeafProofs.L21Aux
