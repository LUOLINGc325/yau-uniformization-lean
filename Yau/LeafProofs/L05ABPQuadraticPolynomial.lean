import Yau.LeafProofs.L05ABPPeanoContacts

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def contactLinear {n : ℕ} (p : Space n) (a0 : ℝ) : Point n →L[ℝ] ℝ :=
  (innerSL ℝ p).comp (ContinuousLinearMap.fst ℝ (Space n) ℝ)+
    a0 • ContinuousLinearMap.snd ℝ (Space n) ℝ

def spatialProjection (n : ℕ) : Point n →L[ℝ] Point n :=
  (ContinuousLinearMap.inl ℝ (Space n) ℝ).comp
    (ContinuousLinearMap.fst ℝ (Space n) ℝ)

def spatialInnerBilin (n : ℕ) : Point n →L[ℝ] Point n →L[ℝ] ℝ :=
  (spaceInnerBilin n).bilinearComp
    (ContinuousLinearMap.fst ℝ (Space n) ℝ)
    (ContinuousLinearMap.fst ℝ (Space n) ℝ)

def temporalInnerBilin (n : ℕ) : Point n →L[ℝ] Point n →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (ContinuousLinearMap.snd ℝ (Space n) ℝ)
    (ContinuousLinearMap.snd ℝ (Space n) ℝ)

def quadraticLiftTimeCoeff {n : ℕ} (eta : ℝ)
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) : ℝ :=
  eta+‖B‖/2+‖B‖^2/(4*eta)

def quadraticLiftBilin {n : ℕ} (delta eta : ℝ)
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) : Point n →L[ℝ] Point n →L[ℝ] ℝ :=
  ((1-8*delta*eta)/2) • B.bilinearComp (spatialProjection n) (spatialProjection n)+
    (8*eta) • spatialInnerBilin n+
    (2*quadraticLiftTimeCoeff eta B) • temporalInnerBilin n

def quadraticLift {n : ℕ} (c : ℝ) (y0 : Point n) (p : Space n)
    (a0 delta eta : ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) : Point n → ℝ :=
  peanoPolynomial (c-(delta/2)*‖p‖^2) y0 (contactLinear p a0)
    (quadraticLiftBilin delta eta B) 0

theorem contactLinear_apply {n : ℕ} (p : Space n) (a0 : ℝ) (v : Point n) :
    contactLinear p a0 v=inner ℝ p v.1+a0*v.2 := rfl

theorem quadraticLiftBilin_apply {n : ℕ} (delta eta : ℝ)
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) (v w : Point n) :
    quadraticLiftBilin delta eta B v w=
      ((1-8*delta*eta)/2)*B (v.1,0) (w.1,0)+
        (8*eta)*inner ℝ v.1 w.1+(2*quadraticLiftTimeCoeff eta B)*v.2*w.2 := by
  simp only [quadraticLiftBilin,add_apply,smul_apply,smul_eq_mul,
    ContinuousLinearMap.bilinearComp_apply,spatialProjection,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.inl_apply,
    spatialInnerBilin,temporalInnerBilin]
  change ((1-8*delta*eta)/2)*B (v.1,0) (w.1,0)+
    (8*eta)*inner ℝ v.1 w.1+(2*quadraticLiftTimeCoeff eta B)*(v.2*w.2)=_
  ring

theorem quadraticLiftBilin_symm {n : ℕ} (delta eta : ℝ)
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) (hB : ∀ v w, B v w=B w v)
    (v w : Point n) : quadraticLiftBilin delta eta B v w=quadraticLiftBilin delta eta B w v := by
  rw [quadraticLiftBilin_apply,quadraticLiftBilin_apply,hB (v.1,0) (w.1,0),
    real_inner_comm v.1 w.1]
  ring

theorem quadraticLift_apply {n : ℕ} (c : ℝ) (y0 : Point n) (p : Space n)
    (a0 delta eta : ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) (y : Point n) :
    quadraticLift c y0 p a0 delta eta B y=
      c-(delta/2)*‖p‖^2+inner ℝ p (y.1-y0.1)+a0*(y.2-y0.2)+
        ((1-8*delta*eta)/4)*B (y.1-y0.1,0) (y.1-y0.1,0)+
        4*eta*‖y.1-y0.1‖^2+quadraticLiftTimeCoeff eta B*(y.2-y0.2)^2 := by
  simp only [quadraticLift,peanoPolynomial,contactLinear_apply,quadraticLiftBilin_apply,
    Prod.fst_sub,Prod.snd_sub,zero_mul,add_zero,real_inner_self_eq_norm_sq]
  ring

theorem quadraticLift_smooth {n : ℕ} (c : ℝ) (y0 : Point n) (p : Space n)
    (a0 delta eta : ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (quadraticLift c y0 p a0 delta eta B) :=
  peanoPolynomial_smooth _ _ _ _ _

theorem quadraticLift_center {n : ℕ} (c : ℝ) (y0 : Point n) (p : Space n)
    (a0 delta eta : ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) :
    quadraticLift c y0 p a0 delta eta B y0=c-(delta/2)*‖p‖^2 := by
  simp [quadraticLift,peanoPolynomial,qnorm2]

theorem quadraticLift_hasFDerivAt {n : ℕ} (c : ℝ) (y0 : Point n) (p : Space n)
    (a0 delta eta : ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w=B w v) :
    HasFDerivAt (quadraticLift c y0 p a0 delta eta B) (contactLinear p a0) y0 := by
  simpa [quadraticLift] using
    peanoPolynomial_hasFDerivAt (c-(delta/2)*‖p‖^2) y0 (contactLinear p a0)
      (quadraticLiftBilin delta eta B) (quadraticLiftBilin_symm delta eta B hB) 0 y0

theorem quadraticLift_timeD {n : ℕ} (c : ℝ) (y0 : Point n) (p : Space n)
    (a0 delta eta : ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w=B w v) :
    timeD Set.univ (quadraticLift c y0 p a0 delta eta B) y0=a0 := by
  rw [quadraticLift,peanoPolynomial_timeD _ _ _ _
    (quadraticLiftBilin_symm delta eta B hB)]
  simp [contactLinear_apply]

theorem jointHessian_coe_apply {n : ℕ}
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) (hB : ∀ v w, B v w=B w v)
    (i j : Yau.RIdx n) :
    (jointHessian B : Mat n) i j=B (Yau.realVec i,0) (Yau.realVec j,0) := by
  let A : Mat n := fun i j => B (Yau.realVec i,0) (Yau.realVec j,0)
  have hsym : IsSelfAdjoint A := by
    apply Matrix.isHermitian_iff_isSelfAdjoint.mp
    ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial]
    exact hB _ _
  have he := IsSelfAdjoint.coe_selfAdjointPart_apply ℝ hsym
  exact congrFun (congrFun he i) j

theorem quadraticLift_hessian_coe {n : ℕ} (c : ℝ) (y0 : Point n) (p : Space n)
    (a0 delta eta : ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w=B w v) (Z : Point n) :
    (hessian (quadraticLift c y0 p a0 delta eta B) Z : Mat n)=
      ((1-8*delta*eta)/2) • (jointHessian B : Mat n)+(8*eta) • (1 : Mat n) := by
  rw [quadraticLift,peanoPolynomial_hessian_coe _ _ _ _
    (quadraticLiftBilin_symm delta eta B hB)]
  simp only [mul_zero,zero_smul,add_zero]
  ext i j
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  rw [jointHessian_coe_apply _ (quadraticLiftBilin_symm delta eta B hB),quadraticLiftBilin_apply,
    jointHessian_coe_apply B hB]
  change ((1-8*delta*eta)/2)*B (Yau.realVec i,0) (Yau.realVec j,0)+
    (8*eta)*inner ℝ (Yau.realVec i) (Yau.realVec j)+(2*quadraticLiftTimeCoeff eta B)*0*0=
    ((1-8*delta*eta)/2)*B (Yau.realVec i,0) (Yau.realVec j,0)+(8*eta)*(if i=j then 1 else 0)
  have hi := (complexVector_realOrthonormalBasis n).inner_eq_ite i j
  simp only [complexVector_realOrthonormalBasis_apply] at hi
  simp only [hi,mul_zero,add_zero]

theorem quadraticLift_hessian {n : ℕ} (c : ℝ) (y0 : Point n) (p : Space n)
    (a0 delta eta : ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w=B w v) (Z : Point n) :
    hessian (quadraticLift c y0 p a0 delta eta B) Z=
      ((1-8*delta*eta)/2) • jointHessian B+(8*eta) • sym (1 : Mat n) := by
  apply Subtype.ext
  have hi : (sym (1 : Mat n) : Mat n)=1 :=
    IsSelfAdjoint.coe_selfAdjointPart_apply ℝ (IsSelfAdjoint.one _)
  change (hessian (quadraticLift c y0 p a0 delta eta B) Z : Mat n)=
    ((1-8*delta*eta)/2) • (jointHessian B : Mat n)+(8*eta) • (sym (1 : Mat n) : Mat n)
  rw [hi,quadraticLift_hessian_coe c y0 p a0 delta eta B hB Z]

end Yau.LeafProofs.L05Aux
