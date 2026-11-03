import Yau.LeafProofs.L05JetCombinationLocal
import Yau.LeafProofs.L05JetCombinationJensen

open Filter MeasureTheory Asymptotics Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem jet_coordinate_inverse_dist {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Point n ≃L[ℝ] E) (y p : Point n) :
    dist y p≤‖e.symm.toContinuousLinearMap‖*dist (e y) (e p) := by
  rw [dist_eq_norm,dist_eq_norm]
  have h := e.symm.toContinuousLinearMap.le_opNorm (e y-e p)
  simpa only [ContinuousLinearEquiv.coe_coe,map_sub,e.symm_apply_apply] using h

theorem jet_bounded_simultaneous_contact {n : ℕ} {U V phi : Point n → ℝ}
    {p : Point n} {B a b kappa d : ℝ}
    (hU : Continuous U) (hV : Continuous V) (hB : 0<B)
    (hUB : ∀ z, |U z|≤B) (hVB : ∀ z, |V z|≤B)
    (ha : 0<a) (hb : 0<b) (hk : 0<kappa) (hd : 0<d)
    (hphi : ContDiffAt ℝ 2 phi p)
    (ht : touchAbove phi (fun z => a*U z+b*V z) p) :
    ∃ (eps : ℝ) (y : Point n) (l1 l2 : Point n →L[ℝ] ℝ)
      (B1 B2 : Point n →L[ℝ] Point n →L[ℝ] ℝ),
      0<eps ∧ dist y p<d/2 ∧ 4*B*eps<(d/2)^2 ∧
      jointPeanoJet (supRegularize eps U) y l1 B1 ∧
      jointPeanoJet (supRegularize eps V) y l2 B2 ∧
      |a*l1 (0,1)+b*l2 (0,1)-timeD univ phi p|<kappa/2 ∧
      ((hessian phi p : Mat n)+(kappa/4) • (1 : Mat n)-
        (a • (jointHessian B1 : Mat n)+b • (jointHessian B2 : Mat n))).PosSemidef := by
  let sigma := kappa/8
  have hsigma : 0<sigma := by dsimp only [sigma]; positivity
  let l0 := fderiv ℝ phi p
  let B0 := fderiv ℝ (fderiv ℝ phi) p
  have hB0 : ∀ v w, B0 v w=B0 w v := (jet_contDiffAt_peano hphi).1
  let BP := B0+(2*sigma) • jointInnerBilin n
  let P := peanoPolynomial (phi p) p l0 B0 sigma
  obtain ⟨r0,hr0,hStrict⟩ := jet_strict_polynomial_upper hphi ht hsigma
  let s := min (r0/2) (min (d/4) (kappa/(8*(‖BP‖+1))))
  have hs : 0<s := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hsr0 : s<r0 := (min_le_left _ _).trans_lt (by linarith)
  have hsd : s≤d/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hsB : ‖BP‖*s<kappa/4 := by
    have hsb : s≤kappa/(8*(‖BP‖+1)) := (min_le_right _ _).trans (min_le_right _ _)
    have hm := (le_div_iff₀ (by positivity : 0<8*(‖BP‖+1))).mp hsb
    nlinarith [norm_nonneg BP]
  let e := abpEuclideanEquiv n
  let r := s/(2*(‖e.symm.toContinuousLinearMap‖+1))
  have hr : 0<r := by dsimp only [r]; positivity
  have hmr : ‖e.symm.toContinuousLinearMap‖*r<s := by
    have heq : r*(2*(‖e.symm.toContinuousLinearMap‖+1))=s := by
      dsimp only [r]; field_simp
    nlinarith [norm_nonneg e.symm.toContinuousLinearMap]
  have hInside (x) (hx : x ∈ Metric.closedBall (e p) r) : dist (e.symm x) p<s := by
    have h := jet_coordinate_inverse_dist e (e.symm x) p
    rw [e.apply_symm_apply] at h
    exact h.trans_lt ((mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp hx)
      (norm_nonneg _)).trans_lt hmr)
  let C := max 1 ‖e.toContinuousLinearMap‖
  have hC : 0<C := zero_lt_one.trans_le (le_max_left _ _)
  let gamma := sigma*r^2/(2*C^2)
  have hgamma : 0<gamma := by dsimp only [gamma]; positivity
  let aerr := gamma/(4*(a+b))
  have haerr : 0<aerr := by dsimp only [aerr]; positivity
  obtain ⟨eps1,heps1,hErrorU⟩ := jet_sup_uniform_on_closedBall hU hB hUB p
    (by positivity : 0<4*s) haerr
  obtain ⟨eps2,heps2,hErrorV⟩ := jet_sup_uniform_on_closedBall hV hB hVB p
    (by positivity : 0<4*s) haerr
  let eps := min eps1 (min eps2 ((d/2)^2/(4*B)))/2
  have heps : 0<eps := by dsimp only [eps]; positivity
  have hepsSmall : eps< min eps1 (min eps2 ((d/2)^2/(4*B))) := by
    have hmin : 0< min eps1 (min eps2 ((d/2)^2/(4*B))) := by positivity
    dsimp only [eps]; linarith
  have hepsU : eps<eps1 := hepsSmall.trans_le (min_le_left _ _)
  have hepsV : eps<eps2 := hepsSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepsDisp : 4*B*eps<(d/2)^2 := by
    have h := hepsSmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hm := (lt_div_iff₀ (by positivity : 0<4*B)).mp h
    nlinarith only [hm]
  let UE := supRegularize eps U
  let VE := supRegularize eps V
  have hGap : ∀ x ∈ Metric.sphere (e p) r,
      P p-(a*UE p+b*VE p)<P (e.symm x)-(a*UE (e.symm x)+b*VE (e.symm x)) := by
    intro x hx
    let z := e.symm x
    have hDist : dist z p<s := hInside x (Metric.sphere_subset_closedBall hx)
    have hzStrict : z ∈ Metric.closedBall p r0 :=
      Metric.mem_closedBall.mpr ((hDist.trans hsr0).le)
    have hST := hStrict z hzStrict
    change a*U z+b*V z≤P z-(sigma/2)*qnorm2 (z-p) at hST
    have hzApprox : z ∈ Metric.closedBall p ((4*s)/2) :=
      Metric.mem_closedBall.mpr (by linarith)
    have hEU := hErrorU eps heps hepsU z hzApprox
    have hEV := hErrorV eps heps hepsV z hzApprox
    have hDiffU : UE z-U z<aerr := (le_abs_self _).trans_lt hEU
    have hDiffV : VE z-V z<aerr := (le_abs_self _).trans_lt hEV
    have hTotal : a*(UE z-U z)+b*(VE z-V z)<gamma/4 := by
      have hsum := add_lt_add (mul_lt_mul_of_pos_left hDiffU ha) (mul_lt_mul_of_pos_left hDiffV hb)
      have heq : a*aerr+b*aerr=gamma/4 := by dsimp only [aerr]; field_simp
      rwa [heq] at hsum
    have hrNorm : r=‖e (z-p)‖ := by
      have hh := Metric.mem_sphere.mp hx
      change dist x (e p)=r at hh
      rw [dist_eq_norm] at hh
      rw [map_sub,e.apply_symm_apply]
      exact hh.symm
    have hBound : r≤C*‖z-p‖ := by
      rw [hrNorm]
      exact (e.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    have hQBound : r^2≤C^2*qnorm2 (z-p) := by
      have hn := norm_sq_le_qnorm2 (z-p)
      have hh := mul_le_mul_of_nonneg_left hn (sq_nonneg C)
      nlinarith [norm_nonneg (z-p)]
    have hGamEq : gamma*(2*C^2)=sigma*r^2 := by dsimp only [gamma]; field_simp
    have hLower : gamma≤(sigma/2)*qnorm2 (z-p) := by
      have hh := mul_le_mul_of_nonneg_left hQBound hsigma.le
      nlinarith [sq_pos_of_pos hC]
    have hUP := (supRegularize_bounds hU hB.le hUB heps p).1
    have hVP := (supRegularize_bounds hV hB.le hVB heps p).1
    have hAt : P p=a*U p+b*V p := by
      simpa only [P,peanoPolynomial,sub_self,map_zero,qnorm2,Prod.fst_zero,Prod.snd_zero,
        norm_zero,zero_pow (by decide : 2≠0),mul_zero,add_zero] using ht.1
    change P p-(a*UE p+b*VE p)<P z-(a*UE z+b*VE z)
    have huWeight := mul_le_mul_of_nonneg_left hUP ha.le
    have hvWeight := mul_le_mul_of_nonneg_left hVP hb.le
    change a*U p≤a*UE p at huWeight
    change b*V p≤b*VE p at hvWeight
    linarith
  have hSemU : jointSemiconvex (1/eps) UE := by
    change ConvexOn ℝ univ (fun z => UE z+(1/eps/2)*qnorm2 z)
    convert! supRegularize_semiconvex hU hB.le hUB heps using 1
    funext z
    change UE z+(1/eps/2)*qnorm2 z=UE z+qnorm2 z/(2*eps)
    ring
  have hSemV : jointSemiconvex (1/eps) VE := by
    change ConvexOn ℝ univ (fun z => VE z+(1/eps/2)*qnorm2 z)
    convert! supRegularize_semiconvex hV hB.le hVB heps using 1
    funext z
    change VE z+(1/eps/2)*qnorm2 z=VE z+qnorm2 z/(2*eps)
    ring
  obtain ⟨y,ell,l1,l2,B1,B2,hy,hEll,h1,h2,hMax⟩ := jet_simultaneous_peano_contact
    hSemU hSemV ha hb (phi p) p l0 B0 hB0 sigma hr (by positivity : 0<kappa/4) hGap
  have hDistY : dist y p<s :=
    (jet_coordinate_inverse_dist e y p).trans_lt
      ((mul_le_mul_of_nonneg_left hy.le (norm_nonneg _)).trans_lt hmr)
  have hRelations := jet_peano_max_relations (jet_peano_weighted_add h1 h2 a b)
    (peanoPolynomial_smooth (phi p) p l0 B0 sigma) hMax
  refine ⟨eps,y,l1,l2,B1,B2,heps,by linarith,hepsDisp,h1,h2,?_,?_⟩
  · have htphi : timeD univ phi p=l0 (0,1) :=
      jointPeanoJet_timeD (jet_contDiffAt_peano hphi)
    have hTime := jet_polynomial_timeD_error (phi p) p l0 B0 hB0 sigma y
    have hSmall : ‖BP‖*‖y-p‖<kappa/4 := by
      rw [← dist_eq_norm]
      exact (mul_le_mul_of_nonneg_left hDistY.le (norm_nonneg BP)).trans_lt hsB
    have hEllEvalLe : |ell (0,1)|≤‖ell‖ := by
      have hEt : ‖((0,1) : Point n)‖=1 := by simp
      simpa only [Real.norm_eq_abs,hEt,mul_one] using ell.le_opNorm ((0,1) : Point n)
    have hEllEval : |ell (0,1)|<kappa/4 := hEllEvalLe.trans_lt hEll
    have hEval := congrArg (fun L : Point n →L[ℝ] ℝ => L (0,1)) hRelations.1
    simp only [add_apply,smul_apply,sub_apply,smul_eq_mul] at hEval
    rw [← timeD_univ_eq_joint ((peanoPolynomial_smooth (phi p) p l0 B0 sigma).differentiable (by simp) y)] at hEval
    rw [htphi]
    have hAbs := abs_add_le (timeD univ P y-l0 (0,1)) (-ell (0,1))
    change |timeD univ P y-l0 (0,1)|≤‖BP‖*‖y-p‖ at hTime
    calc
      |a*l1 (0,1)+b*l2 (0,1)-l0 (0,1)| =
          |(timeD univ P y-l0 (0,1))+(-ell (0,1))| := by congr 1; linarith [hEval]
      _ ≤ |timeD univ P y-l0 (0,1)|+|ell (0,1)| := by simpa using hAbs
      _ < kappa/2 := by linarith
  · have hm := hRelations.2
    simp only [jet_jointHessian_smul,jointHessian_add,AddSubgroup.coe_add] at hm
    rw [peanoPolynomial_hessian_coe (phi p) p l0 B0 hB0 sigma y,
      ← jet_hessian_eq_joint_at hphi] at hm
    have hCoef : 2*sigma=kappa/4 := by dsimp only [sigma]; ring
    simpa only [hCoef,selfAdjoint.val_smul] using hm

theorem jet_bounded_two_upper_tests {n : ℕ} {U V phi : Point n → ℝ}
    {p : Point n} {B a b kappa d : ℝ}
    (hU : Continuous U) (hV : Continuous V) (hB : 0<B)
    (hUB : ∀ z, |U z|≤B) (hVB : ∀ z, |V z|≤B)
    (ha : 0<a) (hb : 0<b) (hk : 0<kappa) (hd : 0<d)
    (hphi : ContDiffAt ℝ 2 phi p)
    (ht : touchAbove phi (fun z => a*U z+b*V z) p) :
    ∃ (q1 q2 : Point n) (psi1 psi2 : Point n → ℝ),
      dist q1 p<d ∧ dist q2 p<d ∧ ContDiff ℝ ∞ psi1 ∧ ContDiff ℝ ∞ psi2 ∧
      touchAbove psi1 U q1 ∧ touchAbove psi2 V q2 ∧
      |a*timeD univ psi1 q1+b*timeD univ psi2 q2-timeD univ phi p|<kappa ∧
      ((hessian phi p : Mat n)+kappa • (1 : Mat n)-
        (a • (hessian psi1 q1 : Mat n)+b • (hessian psi2 q2 : Mat n))).PosSemidef := by
  obtain ⟨eps,y,l1,l2,B1,B2,heps,hy,hDisp,h1,h2,hTime,hMat⟩ :=
    jet_bounded_simultaneous_contact hU hV hB hUB hVB ha hb hk hd hphi ht
  let eta := kappa/(8*(a+b))
  have heta : 0<eta := by dsimp only [eta]; positivity
  let R1 := peanoPolynomial (supRegularize eps U y) y l1 B1 eta
  let R2 := peanoPolynomial (supRegularize eps V y) y l2 B2 eta
  obtain ⟨q1,hq1,_,hDist1⟩ := supRegularize_attained hU hB.le hUB heps y
  obtain ⟨q2,hq2,_,hDist2⟩ := supRegularize_attained hV hB.le hVB heps y
  have hNear (q : Point n) (hq : qnorm2 (y-q)≤4*B*eps) : dist q y<d/2 := by
    have h := (norm_sq_le_qnorm2 (y-q)).trans hq
    rw [dist_eq_norm,norm_sub_rev]
    nlinarith [norm_nonneg (y-q)]
  let psi1 := fun z => R1 (z+(y-q1))+qnorm2 (y-q1)/(2*eps)
  let psi2 := fun z => R2 (z+(y-q2))+qnorm2 (y-q2)/(2*eps)
  have hSmooth1 : ContDiff ℝ ∞ psi1 := by
    dsimp only [psi1,R1]
    exact ((peanoPolynomial_smooth _ _ _ _ _).comp (contDiff_id.add contDiff_const)).add contDiff_const
  have hSmooth2 : ContDiff ℝ ∞ psi2 := by
    dsimp only [psi2,R2]
    exact ((peanoPolynomial_smooth _ _ _ _ _).comp (contDiff_id.add contDiff_const)).add contDiff_const
  have hShift1 : q1+(y-q1)=y := by abel
  have hShift2 : q2+(y-q2)=y := by abel
  have ht1 : timeD univ psi1 q1=l1 (0,1) := by
    rw [timeD_translate,hShift1]
    exact peanoPolynomial_timeD _ _ _ _ h1.1 _
  have ht2 : timeD univ psi2 q2=l2 (0,1) := by
    rw [timeD_translate,hShift2]
    exact peanoPolynomial_timeD _ _ _ _ h2.1 _
  have hm1 : (hessian psi1 q1 : Mat n)=(jointHessian B1 : Mat n)+(2*eta) • (1 : Mat n) := by
    rw [hessian_translate,hShift1]
    exact peanoPolynomial_hessian_coe _ _ _ _ h1.1 _ _
  have hm2 : (hessian psi2 q2 : Mat n)=(jointHessian B2 : Mat n)+(2*eta) • (1 : Mat n) := by
    rw [hessian_translate,hShift2]
    exact peanoPolynomial_hessian_coe _ _ _ _ h2.1 _ _
  refine ⟨q1,q2,psi1,psi2,?_,?_,hSmooth1,hSmooth2,?_,?_,?_,?_⟩
  · exact (dist_triangle q1 y p).trans_lt (by linarith [hNear q1 hDist1])
  · exact (dist_triangle q2 y p).trans_lt (by linarith [hNear q2 hDist2])
  · exact supRegularize_upper_touch hU hB.le hUB heps hq1 (jointPeanoJet_upper_test h1 heta)
  · exact supRegularize_upper_touch hV hB.le hVB heps hq2 (jointPeanoJet_upper_test h2 heta)
  · rw [ht1,ht2]
    exact hTime.trans (by linarith)
  · rw [hm1,hm2]
    have hPad : ((kappa/2) • (1 : Mat n)).PosSemidef := Matrix.PosSemidef.one.smul (by positivity)
    have hCoef : 2*eta*(a+b)=kappa/4 := by dsimp only [eta]; field_simp; ring
    convert! hMat.add hPad using 1
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    linear_combination -((1 : Mat n) i j)*hCoef

theorem jet_exists_two_upper_tests
    {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {u v phi : Point n → ℝ} {p : Point n}
    (hp : p ∈ Q) (hu : ContinuousOn u Q) (hv : ContinuousOn v Q)
    {a b kappa : ℝ} (ha : 0<a) (hb : 0<b) (hk : 0<kappa)
    (hphi : ContDiffAt ℝ 2 phi p)
    (ht : touchAbove phi (fun z => a*u z+b*v z) p) :
    ∃ (q1 q2 : Point n) (psi1 psi2 : Point n → ℝ),
      q1 ∈ Q ∧ q2 ∈ Q ∧ dist q1 p<kappa ∧ dist q2 p<kappa ∧
      ContDiff ℝ ∞ psi1 ∧ ContDiff ℝ ∞ psi2 ∧
      touchAbove psi1 u q1 ∧ touchAbove psi2 v q2 ∧
      |a*timeD univ psi1 q1+b*timeD univ psi2 q2-timeD univ phi p|<kappa ∧
      ((hessian phi p : Mat n)+kappa • (1 : Mat n)-
        (a • (hessian psi1 q1 : Mat n)+b • (hessian psi2 q2 : Mat n))).PosSemidef := by
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds hp)
  let R := r/2
  have hR : 0<R := by dsimp only [R]; positivity
  have hClosed : Metric.closedBall p R ⊆ Q :=
    (Metric.closedBall_subset_ball (by dsimp only [R]; linarith : R<r)).trans hBall
  obtain ⟨BU,U,hBU,hU,hUB,hEqU⟩ := jet_exists_bounded_extension (isCompact_closedBall p R)
    (hu.mono hClosed)
  obtain ⟨BV,V,hBV,hV,hVB,hEqV⟩ := jet_exists_bounded_extension (isCompact_closedBall p R)
    (hv.mono hClosed)
  let B := max BU BV
  have hB : 0<B := hBU.trans_le (le_max_left _ _)
  have hUB' (z) : |U z|≤B := (hUB z).trans (le_max_left _ _)
  have hVB' (z) : |V z|≤B := (hVB z).trans (le_max_right _ _)
  have hEq (q : Point n) (hq : q ∈ Metric.ball p R) :
      U =ᶠ[𝓝 q] u ∧ V =ᶠ[𝓝 q] v := by
    have hNhd : Metric.closedBall p R ∈ 𝓝 q :=
      mem_of_superset (Metric.isOpen_ball.mem_nhds hq) Metric.ball_subset_closedBall
    exact ⟨jet_eventuallyEq_of_eqOn hEqU hNhd,jet_eventuallyEq_of_eqOn hEqV hNhd⟩
  have hEqP := hEq p (Metric.mem_ball_self hR)
  have hTouch : touchAbove phi (fun z => a*U z+b*V z) p := by
    refine ⟨?_,?_⟩
    · change phi p=a*U p+b*V p
      rw [hEqP.1.eq_of_nhds,hEqP.2.eq_of_nhds]
      exact ht.1
    · filter_upwards [hEqP.1,hEqP.2,ht.2] with z hzU hzV hz
      rwa [hzU,hzV]
  obtain ⟨q1,q2,psi1,psi2,hq1,hq2,hs1,hs2,ht1,ht2,hTime,hMat⟩ :=
    jet_bounded_two_upper_tests hU hV hB hUB' hVB' ha hb hk
      (lt_min hk hR) hphi hTouch
  have hq1R : q1 ∈ Metric.ball p R :=
    Metric.mem_ball.mpr (hq1.trans_le (min_le_right _ _))
  have hq2R : q2 ∈ Metric.ball p R :=
    Metric.mem_ball.mpr (hq2.trans_le (min_le_right _ _))
  exact ⟨q1,q2,psi1,psi2,hClosed (Metric.ball_subset_closedBall hq1R),
    hClosed (Metric.ball_subset_closedBall hq2R),hq1.trans_le (min_le_left _ _),
    hq2.trans_le (min_le_left _ _),hs1,hs2,
    jet_touchAbove_of_eventuallyEq (hEq q1 hq1R).1 ht1,
    jet_touchAbove_of_eventuallyEq (hEq q2 hq2R).2 ht2,hTime,hMat⟩

end Yau.LeafProofs.L05Aux
