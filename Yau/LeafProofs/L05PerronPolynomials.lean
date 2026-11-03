import Yau.LeafProofs.L05PerronClassical
import Yau.LeafProofs.L05ABPRetraction

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def perronSeparatedBilin (n : ℕ) (k d : ℝ) : Point n →L[ℝ] Point n →L[ℝ] ℝ :=
  (2*k) • spatialInnerBilin n+(2*d) • temporalInnerBilin n

def perronSeparatedPolynomial {n : ℕ} (c : ℝ) (p : Point n) (v : Space n) (a k d : ℝ) :
    Point n → ℝ := peanoPolynomial c p (contactLinear v a) (perronSeparatedBilin n k d) 0

theorem perronSeparatedBilin_apply {n : ℕ} (k d : ℝ) (v w : Point n) :
    perronSeparatedBilin n k d v w=(2*k)*inner ℝ v.1 w.1+(2*d)*v.2*w.2 := by
  change (2*k)*inner ℝ v.1 w.1+(2*d)*(v.2*w.2)=_
  ring

theorem perronSeparatedBilin_symm {n : ℕ} (k d : ℝ) (v w : Point n) :
    perronSeparatedBilin n k d v w=perronSeparatedBilin n k d w v := by
  rw [perronSeparatedBilin_apply,perronSeparatedBilin_apply,real_inner_comm v.1 w.1]
  ring

theorem perronSeparatedPolynomial_apply {n : ℕ} (c : ℝ) (p : Point n) (v : Space n)
    (a k d : ℝ) (q : Point n) :
    perronSeparatedPolynomial c p v a k d q=
      c+inner ℝ v (q.1-p.1)+a*(q.2-p.2)+k*‖q.1-p.1‖^2+d*(q.2-p.2)^2 := by
  simp only [perronSeparatedPolynomial,peanoPolynomial,contactLinear_apply,
    perronSeparatedBilin_apply,Prod.fst_sub,Prod.snd_sub,zero_mul,add_zero,
    real_inner_self_eq_norm_sq]
  ring

theorem perronSeparatedPolynomial_smooth {n : ℕ} (c : ℝ) (p : Point n) (v : Space n)
    (a k d : ℝ) : ContDiff ℝ ∞ (perronSeparatedPolynomial c p v a k d) :=
  peanoPolynomial_smooth _ _ _ _ _

theorem perronSeparatedPolynomial_center {n : ℕ} (c : ℝ) (p : Point n) (v : Space n)
    (a k d : ℝ) : perronSeparatedPolynomial c p v a k d p=c := by
  simp [perronSeparatedPolynomial,peanoPolynomial,qnorm2]

theorem perronSeparatedPolynomial_timeD {n : ℕ} (c : ℝ) (p : Point n) (v : Space n)
    (a k d : ℝ) (q : Point n) :
    timeD Set.univ (perronSeparatedPolynomial c p v a k d) q=a+2*d*(q.2-p.2) := by
  have hd := peanoPolynomial_hasFDerivAt c p (contactLinear v a) (perronSeparatedBilin n k d)
    (perronSeparatedBilin_symm k d) 0 q
  change timeD Set.univ (peanoPolynomial c p (contactLinear v a) (perronSeparatedBilin n k d) 0) q=_
  rw [timeD_univ_eq_joint hd.differentiableAt,hd.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,contactLinear_apply,perronSeparatedBilin_apply,
    Prod.fst_sub,Prod.snd_sub,inner_zero_right,mul_zero,zero_add,mul_one,add_zero]
  ring

theorem perronSeparatedPolynomial_hessian_coe {n : ℕ} (c : ℝ) (p : Point n) (v : Space n)
    (a k d : ℝ) (q : Point n) :
    (hessian (perronSeparatedPolynomial c p v a k d) q : Mat n)=(2*k) • (1 : Mat n) := by
  rw [perronSeparatedPolynomial,peanoPolynomial_hessian_coe _ _ _ _
    (perronSeparatedBilin_symm k d)]
  simp only [mul_zero,zero_smul,add_zero]
  ext i j
  rw [jointHessian_coe_apply _ (perronSeparatedBilin_symm k d),perronSeparatedBilin_apply]
  change (2*k)*inner ℝ (Yau.realVec i) (Yau.realVec j)+(2*d)*0*0=
    (2*k)*(if i=j then 1 else 0)
  have hi := (complexVector_realOrthonormalBasis n).inner_eq_ite i j
  simp only [complexVector_realOrthonormalBasis_apply] at hi
  rw [hi]
  ring

theorem perronSeparatedPolynomial_hessian {n : ℕ} (c : ℝ) (p : Point n) (v : Space n)
    (a k d : ℝ) (q : Point n) :
    hessian (perronSeparatedPolynomial c p v a k d) q=(2*k) • sym (1 : Mat n) := by
  apply Subtype.ext
  change (hessian (perronSeparatedPolynomial c p v a k d) q : Mat n)=
    (2*k) • (sym (1 : Mat n) : Mat n)
  have hi : (sym (1 : Mat n) : Mat n)=1 :=
    IsSelfAdjoint.coe_selfAdjointPart_apply ℝ (IsSelfAdjoint.one _)
  rw [hi,perronSeparatedPolynomial_hessian_coe]

def perronInitialShape {n : ℕ} (p : Point n) (kappa : ℝ) : Point n → ℝ :=
  perronSeparatedPolynomial 0 p 0 kappa 1 0

def perronLateralShape {n : ℕ} (p : Point n) (K : ℝ) : Point n → ℝ :=
  perronSeparatedPolynomial 0 p ((-(1+2*K)) • p.1) 0 (-K) 1

theorem perronInitialShape_apply {n : ℕ} (p q : Point n) (kappa : ℝ) :
    perronInitialShape p kappa q=‖q.1-p.1‖^2+kappa*(q.2-p.2) := by
  rw [perronInitialShape,perronSeparatedPolynomial_apply]
  simp only [inner_zero_left,zero_add,zero_mul,add_zero,one_mul]
  ring

theorem perronLateralShape_apply {n : ℕ} {p : Point n} (hp : ‖p.1‖=1) (q : Point n) (K : ℝ) :
    perronLateralShape p K q=
      1-inner ℝ q.1 p.1+K*(1-‖q.1‖^2)+(q.2-p.2)^2 := by
  rw [perronLateralShape,perronSeparatedPolynomial_apply]
  simp only [inner_smul_left,conj_trivial,smul_eq_mul,inner_sub_right,
    real_inner_self_eq_norm_sq,norm_sub_sq_real,hp,one_pow,zero_add,zero_mul,add_zero,one_mul]
  rw [real_inner_comm p.1 q.1]
  ring

theorem perronInitialShape_distance {n : ℕ} {p q : Point n} {kappa : ℝ}
    (hp : p.2=(-1:ℝ)) (hq : q∈abpClosed n 1 (-1) 1) (hk : 2≤kappa) :
    dist q p^2≤perronInitialShape p kappa q := by
  have ht0 : 0≤q.2-p.2 := by linarith [hq.2.1]
  have ht2 : q.2-p.2≤2 := by linarith [hq.2.2]
  have hm := mul_nonneg (sub_nonneg.mpr hk) ht0
  have htime := mul_nonneg ht0 (sub_nonneg.mpr ht2)
  have hn := norm_sq_le_qnorm2 (q-p)
  rw [perronInitialShape_apply,dist_eq_norm]
  simp only [qnorm2,Prod.fst_sub,Prod.snd_sub] at hn
  change ‖q-p‖^2≤‖q.1-p.1‖^2+kappa*(q.2-p.2)
  nlinarith

theorem perronLateralShape_distance {n : ℕ} {p q : Point n} {K : ℝ}
    (hp : ‖p.1‖=1) (hq : q∈abpClosed n 1 (-1) 1) (hK : 0≤K) :
    dist q p^2/2≤perronLateralShape p K q := by
  have hqn : ‖q.1‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hq.1
  have hq2 : ‖q.1‖^2≤1 := by nlinarith [norm_nonneg q.1]
  have hKn := mul_nonneg hK (sub_nonneg.mpr hq2)
  have hn := norm_sq_le_qnorm2 (q-p)
  simp only [qnorm2,Prod.fst_sub,Prod.snd_sub] at hn
  rw [perronLateralShape_apply hp,dist_eq_norm]
  have he := norm_sub_sq_real q.1 p.1
  rw [hp,one_pow] at he
  nlinarith [sq_nonneg (q.2-p.2)]

end Yau.LeafProofs.L05Aux
