import Yau.LeafProofs.L05JetCombinationApprox
import Yau.LeafProofs.L05JetCombinationMatrix

open Filter MeasureTheory Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem jet_le_zero_of_positive_tolerances {A C : ℝ} (hC : 0<C)
    (h : ∀ kappa : ℝ, 0<kappa → A≤kappa*C) : A≤0 := by
  by_contra hA
  have hApos : 0<A := lt_of_not_ge hA
  have hbound := h (A/(2*C)) (by positivity)
  have heq : (A/(2*C))*C=A/2 := by field_simp
  rw [heq] at hbound
  linarith

theorem jet_autonomous_difference_sub
    {n : ℕ} {Q : Set (Point n)} {F : Sym n → ℝ} {ell L : ℝ}
    (hQ : IsOpen Q) (hell : 0≤ell) (hL : ell≤L) (hF : globalElliptic F ell L)
    {u v : Point n → ℝ} (hu : ContinuousOn u Q) (hv : ContinuousOn v Q)
    (hsub : viscositySub Q (fun H _ => F H) (fun _ => 0) u)
    (hsuper : viscositySuper Q (fun H _ => F H) (fun _ => 0) v) :
    viscositySub Q (fun H _ => pucciPlus ell L H) (fun _ => 0) (u-v) := by
  intro p hp phi hphi ht
  have hConst : 0<1+(2*n : ℝ)*L := by
    have hn : 0≤(2*n : ℝ)*L := mul_nonneg (by positivity) (hell.trans hL)
    linarith
  apply jet_le_zero_of_positive_tolerances hConst
  intro kappa hk
  have htWeighted : touchAbove phi (fun z => 1*u z+1*(-v) z) p := by
    convert! ht using 1
    funext z
    simp only [one_mul,Pi.neg_apply,Pi.sub_apply,sub_eq_add_neg]
  obtain ⟨q1,q2,psi1,psi2,hq1,hq2,_,_,hs1,hs2,ht1,ht2,hTime,hMat⟩ :=
    jet_exists_two_upper_tests hQ hp hu hv.neg (by norm_num : (0:ℝ)<1)
      (by norm_num : (0:ℝ)<1) hk hphi htWeighted
  have htLower : touchBelow (-psi2) v q2 := by
    refine ⟨?_,?_⟩
    · change -psi2 q2=v q2
      have he := ht2.1
      change psi2 q2 = -v q2 at he
      linarith
    · filter_upwards [ht2.2] with z hz
      change -psi2 z≤v z
      change -v z≤psi2 z at hz
      linarith
  have hsNeg : ContDiff ℝ ∞ (-psi2) := by convert! hs2.neg using 1
  have hSub := hsub q1 hq1 psi1 (hs1.contDiffAt.of_le (by simp)) ht1
  have hSuper := hsuper q2 hq2 (-psi2) (hsNeg.contDiffAt.of_le (by simp)) htLower
  change timeD univ psi1 q1-F (hessian psi1 q1)≤0 at hSub
  change 0≤timeD univ (-psi2) q2-F (hessian (-psi2) q2) at hSuper
  rw [jet_timeD_neg_smooth hs2,jet_hessian_neg_smooth hs2] at hSuper
  have hFDiff := jet_elliptic_difference_le_pucci hell hL hF (hessian psi1 q1) (-hessian psi2 q2)
  simp only [sub_neg_eq_add] at hFDiff
  have hMatrix : ((hessian phi p : Mat n)+kappa • (1 : Mat n)-
      ((hessian psi1 q1+hessian psi2 q2 : Sym n) : Mat n)).PosSemidef := by
    simpa only [one_smul,AddSubgroup.coe_add] using hMat
  have hPucci := jet_pucci_le_of_matrix_le hell hL hk.le hMatrix
  simp only [one_mul] at hTime
  have hError := (neg_le_abs (timeD univ psi1 q1+timeD univ psi2 q2-timeD univ phi p)).trans hTime.le
  change timeD univ phi p-pucciPlus ell L (hessian phi p)≤kappa*(1+(2*n : ℝ)*L)
  nlinarith only [hSub,hSuper,hFDiff,hPucci,hError]

theorem jet_autonomous_convex_combination_sub
    {n : ℕ} {Q : Set (Point n)} {F : Sym n → ℝ} {ell L : ℝ}
    (hQ : IsOpen Q) (hell : 0≤ell) (hL : ell≤L) (hF : globalElliptic F ell L)
    (hconc : ConcaveOn ℝ univ F) {u v : Point n → ℝ}
    (hu : ContinuousOn u Q) (hv : ContinuousOn v Q)
    (hsubu : viscositySub Q (fun H _ => F H) (fun _ => 0) u)
    (hsubv : viscositySub Q (fun H _ => F H) (fun _ => 0) v)
    {theta : ℝ} (htheta : theta ∈ Icc 0 1) :
    viscositySub Q (fun H _ => F H) (fun _ => 0)
      (fun p => theta*u p+(1-theta)*v p) := by
  by_cases hzero : theta=0
  · subst theta
    simpa only [zero_mul,one_mul,sub_zero,zero_add] using hsubv
  by_cases hone : theta=1
  · subst theta
    simpa only [one_mul,sub_self,zero_mul,add_zero] using hsubu
  have hthetaPos : 0<theta := (lt_or_eq_of_le htheta.1).resolve_right (Ne.symm hzero)
  have hbPos : 0<1-theta := sub_pos.mpr ((lt_or_eq_of_le htheta.2).resolve_right hone)
  intro p hp phi hphi ht
  have hConst : 0<1+(2*n : ℝ)*L := by
    have hn : 0≤(2*n : ℝ)*L := mul_nonneg (by positivity) (hell.trans hL)
    linarith
  apply jet_le_zero_of_positive_tolerances hConst
  intro kappa hk
  obtain ⟨q1,q2,psi1,psi2,hq1,hq2,_,_,hs1,hs2,ht1,ht2,hTime,hMat⟩ :=
    jet_exists_two_upper_tests hQ hp hu hv hthetaPos hbPos hk hphi ht
  have hSub1 := hsubu q1 hq1 psi1 (hs1.contDiffAt.of_le (by simp)) ht1
  have hSub2 := hsubv q2 hq2 psi2 (hs2.contDiffAt.of_le (by simp)) ht2
  change timeD univ psi1 q1-F (hessian psi1 q1)≤0 at hSub1
  change timeD univ psi2 q2-F (hessian psi2 q2)≤0 at hSub2
  have hWeight1 := mul_le_mul_of_nonneg_left hSub1 hthetaPos.le
  have hWeight2 := mul_le_mul_of_nonneg_left hSub2 hbPos.le
  have hConc : theta*F (hessian psi1 q1)+(1-theta)*F (hessian psi2 q2)≤
      F (theta • hessian psi1 q1+(1-theta) • hessian psi2 q2) := by
    simpa only [smul_eq_mul] using hconc.2
      (show hessian psi1 q1 ∈ univ from mem_univ _)
      (show hessian psi2 q2 ∈ univ from mem_univ _) hthetaPos.le hbPos.le (by ring)
  have hMatrix : ((hessian phi p : Mat n)+kappa • (1 : Mat n)-
      ((theta • hessian psi1 q1+(1-theta) • hessian psi2 q2 : Sym n) : Mat n)).PosSemidef := by
    simpa only [AddSubgroup.coe_add,selfAdjoint.val_smul] using hMat
  have hFBound := jet_elliptic_le_of_matrix_le hell hF hk.le hMatrix
  have hError := (neg_le_abs (theta*timeD univ psi1 q1+(1-theta)*timeD univ psi2 q2-
    timeD univ phi p)).trans hTime.le
  change timeD univ phi p-F (hessian phi p)≤kappa*(1+(2*n : ℝ)*L)
  nlinarith only [hWeight1,hWeight2,hConc,hFBound,hError]

theorem parabolicJetCombination : ParabolicJetCombinationGap := by
  intro n _hn ell L hell hL Q F hQ _hFcont hF
  constructor
  · intro u v hu hv hsub hsuper
    exact jet_autonomous_difference_sub hQ hell.le hL hF hu hv hsub hsuper
  · intro hconc u v hu hv hsubu hsubv theta htheta
    exact jet_autonomous_convex_combination_sub hQ hell.le hL hF hconc hu hv hsubu hsubv htheta

end Yau.LeafProofs.L05Aux
