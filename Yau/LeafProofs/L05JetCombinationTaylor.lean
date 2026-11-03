import Yau.LeafProofs.L05ABPPeanoContacts

open Filter MeasureTheory Asymptotics Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

/-- A genuinely local joint C² test has its actual second Peano expansion
in the given product norm; no inner product on the joint product is used. -/
theorem jet_contDiffAt_peano {n : ℕ} {phi : Point n → ℝ} {p : Point n}
    (hphi : ContDiffAt ℝ 2 phi p) :
    jointPeanoJet phi p (fderiv ℝ phi p) (fderiv ℝ (fderiv ℝ phi) p) := by
  let l := fderiv ℝ phi p
  let B := fderiv ℝ (fderiv ℝ phi) p
  have hB : ∀ v w, B v w = B w v := hphi.isSymmSndFDerivAt (by norm_num)
  have hD : HasFDerivAt (fderiv ℝ phi) B p :=
    ((hphi.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hEventually : ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ phi y := by
    filter_upwards [hphi.eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp hEventually
  let R : Point n → ℝ := fun y => phi y-phi p-l (y-p)-(1/2 : ℝ)*B (y-p) (y-p)
  let R' : Point n → Point n →L[ℝ] ℝ := fun y => fderiv ℝ phi y-l-B (y-p)
  have hR (y : Point n) (hy : y ∈ Metric.ball p r) : HasFDerivAt R (R' y) y := by
    have hShift := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const p
    have hLin := l.hasFDerivAt.comp y hShift
    have hQuad := symmetric_quadratic_hasFDerivAt B hB p y
    convert! ((((hBall hy).hasFDerivAt).sub_const (phi p)).sub hLin).sub hQuad using 1
  have hSmall : R' =o[𝓝 p] (fun y => ‖y-p‖^1) := by
    simpa only [R',l,pow_one,isLittleO_norm_right] using hasFDerivAt_iff_isLittleO.mp hD
  have hWithin : 𝓝[Metric.ball p r] p = 𝓝 p :=
    nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds p hr)
  have hSmallWithin : R' =o[𝓝[Metric.ball p r] p] (fun y => ‖y-p‖^1) := by
    rw [hWithin]
    exact hSmall
  have hFinal := (convex_ball p r).isLittleO_pow_succ (n := 1) (Metric.mem_ball_self hr)
    (fun y hy => (hR y hy).hasFDerivWithinAt) hSmallWithin
  have hRp : R p = 0 := by simp [R]
  rw [hWithin,hRp] at hFinal
  refine ⟨hB,?_⟩
  simpa only [R,sub_zero] using hFinal

theorem jet_spatialDD_eq_joint_second_at {n : ℕ} {phi : Point n → ℝ} {p : Point n}
    (hphi : ContDiffAt ℝ 2 phi p) :
    spatialDD phi p = (fderiv ℝ (fderiv ℝ phi) p).bilinearComp
      (ContinuousLinearMap.inl ℝ (Space n) ℝ) (ContinuousLinearMap.inl ℝ (Space n) ℝ) := by
  let i := ContinuousLinearMap.inl ℝ (Space n) ℝ
  have hd := ((hphi.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc := hd.clm_comp (hasFDerivAt_const i p)
  have hi : HasFDerivAt (fun x : Space n => (x,p.2)) i p.1 := by
    simpa only [i,ContinuousLinearMap.inl_apply,Prod.mk_add_mk,zero_add,add_zero] using
      (i.hasFDerivAt (x := p.1)).add_const ((0,p.2) : Point n)
  have hs := hc.comp p.1 hi
  have hDiff : ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ phi y := by
    filter_upwards [hphi.eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hLine : Tendsto (fun x : Space n => (x,p.2)) (𝓝 p.1) (𝓝 p) := by
    simpa only [Prod.eta,id_eq] using (continuous_id.prodMk continuous_const).tendsto p.1
  have hEq : (fun x : Space n => spatialD phi (x,p.2)) =ᶠ[𝓝 p.1]
      (fun x : Space n => (fderiv ℝ phi (x,p.2)).comp i) := by
    filter_upwards [hLine hDiff] with x hx
    exact spatialD_eq_joint hx
  change fderiv ℝ (fun x : Space n => spatialD phi (x,p.2)) p.1 = _
  rw [hEq.fderiv_eq]
  have hsf := hs.fderiv
  simp only [Function.comp_def] at hsf
  rw [hsf]
  ext v w
  simp [i,ContinuousLinearMap.bilinearComp_apply]

theorem jet_hessian_eq_joint_at {n : ℕ} {phi : Point n → ℝ} {p : Point n}
    (hphi : ContDiffAt ℝ 2 phi p) :
    hessian phi p = jointHessian (fderiv ℝ (fderiv ℝ phi) p) := by
  unfold hessian jointHessian
  rw [jet_spatialDD_eq_joint_second_at hphi]
  rfl

theorem jet_strict_polynomial_upper {n : ℕ} {w phi : Point n → ℝ} {p : Point n}
    (hphi : ContDiffAt ℝ 2 phi p) (ht : touchAbove phi w p)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Metric.closedBall p r,
      w z ≤ peanoPolynomial (phi p) p (fderiv ℝ phi p)
        (fderiv ℝ (fderiv ℝ phi) p) sigma z-(sigma/2)*qnorm2 (z-p) := by
  have hJet := jet_contDiffAt_peano hphi
  have hGood : ∀ᶠ z in 𝓝 p, w z ≤ phi z ∧
      ‖phi z-phi p-fderiv ℝ phi p (z-p)-
        (1/2 : ℝ)*fderiv ℝ (fderiv ℝ phi) p (z-p) (z-p)‖ ≤
        (sigma/2)*‖‖z-p‖^2‖ := ht.2.and (hJet.2.bound (by positivity : 0 < sigma/2))
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp hGood
  refine ⟨r/2,by positivity,?_⟩
  intro z hz
  have h := hBall (Metric.closedBall_subset_ball (by linarith : r/2 < r) hz)
  have hR := (le_abs_self (phi z-phi p-fderiv ℝ phi p (z-p)-
    (1/2 : ℝ)*fderiv ℝ (fderiv ℝ phi) p (z-p) (z-p))).trans
      (by simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using h.2)
  have hQ := mul_le_mul_of_nonneg_left (norm_sq_le_qnorm2 (z-p)) (by positivity : 0 ≤ sigma/2)
  dsimp only [peanoPolynomial]
  linarith only [h.1,hR,hQ]

theorem jet_peano_weighted_add {n : ℕ} {U V : Point n → ℝ} {y : Point n}
    {l1 l2 : Point n →L[ℝ] ℝ} {B1 B2 : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (h1 : jointPeanoJet U y l1 B1) (h2 : jointPeanoJet V y l2 B2) (a b : ℝ) :
    jointPeanoJet (fun z => a*U z+b*V z) y (a • l1+b • l2) (a • B1+b • B2) := by
  refine ⟨?_,?_⟩
  · intro v w
    simp only [add_apply,smul_apply,smul_eq_mul]
    rw [h1.1 v w,h2.1 v w]
  · have h := (h1.2.const_mul_left a).add (h2.2.const_mul_left b)
    convert h using 1
    funext z
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring

theorem jet_jointHessian_smul {n : ℕ} (c : ℝ)
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) : jointHessian (c • B) = c • jointHessian B := by
  let A : Mat n := fun i j => B (Yau.realVec i,0) (Yau.realVec j,0)
  let S : Mat n →ₗ[ℝ] Sym n := selfAdjointPart ℝ
  have hMatrix : ((fun i j : Yau.RIdx n => (c • B) (Yau.realVec i,0) (Yau.realVec j,0)) : Mat n) =
      c • A := by
    ext i j
    simp only [smul_apply,smul_eq_mul]
    rfl
  exact (congrArg S hMatrix).trans (S.map_smul c A)

theorem jet_jointHessian_neg {n : ℕ}
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) : jointHessian (-B) = -jointHessian B := by
  have h := jet_jointHessian_smul (-1) B
  have he : (-1 : ℝ) • B = -B := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp only [smul_apply,neg_apply,smul_eq_mul,neg_one_mul]
  rw [he] at h
  exact h.trans (neg_one_smul ℝ (jointHessian B))

theorem jet_hessian_neg_smooth {n : ℕ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) (y : Point n) : hessian (-u) y = -hessian u y := by
  have hf : fderiv ℝ (-u) = -fderiv ℝ u := by funext q; exact fderiv_neg
  have hn : ContDiff ℝ ∞ (-u) := by convert! hu.neg using 1
  rw [hessian_eq_jointHessian hn,hessian_eq_jointHessian hu,hf,fderiv_neg,
    jet_jointHessian_neg]

theorem jet_hessian_sub_smooth {n : ℕ} {u v : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (y : Point n) :
    hessian (u-v) y = hessian u y-hessian v y := by
  have hn : ContDiff ℝ ∞ (-v) := by convert! hv.neg using 1
  rw [sub_eq_add_neg,hessian_add_smooth hu hn,jet_hessian_neg_smooth hv,sub_eq_add_neg]

theorem jet_hessian_clm {n : ℕ} (ell : Point n →L[ℝ] ℝ) (y : Point n) :
    hessian ell y = 0 := by
  rw [hessian_eq_jointHessian ell.contDiff]
  have hf : fderiv ℝ ell = fun _ => ell := by funext q; exact ell.fderiv
  rw [hf]
  have hc : fderiv ℝ (fun _ : Point n => ell) y=0 := by simp
  rw [hc]
  exact (selfAdjointPart ℝ).map_zero

theorem jet_timeD_neg_smooth {n : ℕ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) (y : Point n) : timeD univ (-u) y = -timeD univ u y := by
  have hn : ContDiff ℝ ∞ (-u) := by convert! hu.neg using 1
  rw [timeD_univ_eq_joint (hn.differentiable (by simp) y),
    timeD_univ_eq_joint (hu.differentiable (by simp) y),fderiv_neg,neg_apply]

theorem jet_polynomial_timeD {n : ℕ} (c : ℝ) (p : Point n)
    (l : Point n →L[ℝ] ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (sigma : ℝ) (y : Point n) :
    timeD univ (peanoPolynomial c p l B sigma) y =
      (l+B (y-p)+(2*sigma) • jointInnerBilin n (y-p)) (0,1) := by
  rw [timeD_univ_eq_joint (peanoPolynomial_hasFDerivAt c p l B hB sigma y).differentiableAt,
    (peanoPolynomial_hasFDerivAt c p l B hB sigma y).fderiv]

theorem jet_polynomial_timeD_error {n : ℕ} (c : ℝ) (p : Point n)
    (l : Point n →L[ℝ] ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (sigma : ℝ) (y : Point n) :
    |timeD univ (peanoPolynomial c p l B sigma) y-l (0,1)| ≤
      ‖B+(2*sigma) • jointInnerBilin n‖*‖y-p‖ := by
  rw [jet_polynomial_timeD c p l B hB sigma y]
  have he : (l+B (y-p)+(2*sigma) • jointInnerBilin n (y-p)) (0,1)-l (0,1) =
      (B+(2*sigma) • jointInnerBilin n) (y-p) (0,1) := by
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring
  rw [he,← Real.norm_eq_abs]
  have h := ContinuousLinearMap.le_opNorm₂ (B+(2*sigma) • jointInnerBilin n)
    (y-p) ((0,1) : Point n)
  simpa using h

theorem jet_peano_max_relations {n : ℕ} {W P : Point n → ℝ} {y : Point n}
    {l ell : Point n →L[ℝ] ℝ} {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (hW : jointPeanoJet W y l B) (hP : ContDiff ℝ ∞ P)
    (hm : IsLocalMax (fun z => W z-P z+ell z) y) :
    l = fderiv ℝ P y-ell ∧
      ((hessian P y : Mat n)-(jointHessian B : Mat n)).PosSemidef := by
  have hDer := ((jointPeanoJet_hasFDerivAt hW).sub
    (hP.differentiable (by simp) y).hasFDerivAt).add ell.hasFDerivAt
  have he : l-fderiv ℝ P y+ell=0 := hDer.fderiv.symm.trans hm.fderiv_eq_zero
  refine ⟨?_,?_⟩
  · calc
      l = (l-fderiv ℝ P y+ell)+(fderiv ℝ P y-ell) := by abel
      _ = fderiv ℝ P y-ell := by rw [he,zero_add]
  have hRho (rho : ℝ) (hrho : 0<rho) :
      ((hessian P y : Mat n)-(jointHessian B : Mat n)+(2*rho) • (1 : Mat n)).PosSemidef := by
    let A := peanoPolynomial (W y) y l B (-rho)
    have hA : ContDiff ℝ ∞ A := peanoPolynomial_smooth _ _ _ _ _
    have hlow := jointPeanoJet_lower_test hW hrho
    have hpath : Tendsto (fun x : Space n => (x,y.2)) (𝓝 y.1) (𝓝 y) := by
      simpa only [Prod.eta,id_eq] using (continuous_id.prodMk continuous_const).tendsto y.1
    have hmax : IsLocalMax (fun x : Space n => (A-P+ell) (x,y.2)) y.1 := by
      filter_upwards [hpath hlow.2,hpath hm] with x hx hxm
      change A (x,y.2)-P (x,y.2)+ell (x,y.2) ≤ A y-P y+ell y
      have ha : A y = W y := by simp [A,peanoPolynomial,qnorm2]
      rw [ha]
      change A (x,y.2)≤W (x,y.2) at hx
      change W (x,y.2)-P (x,y.2)+ell (x,y.2)≤W y-P y+ell y at hxm
      linarith
    have hSub : ContDiff ℝ ∞ (A-P) := by convert! hA.sub hP using 1
    have hSum : ContDiff ℝ ∞ (A-P+(ell : Point n → ℝ)) := by convert! hSub.add ell.contDiff using 1
    have hmat := smooth_spatial_localMax_hessian_nonpos hSum y hmax
    rw [hessian_add_smooth hSub ell.contDiff,jet_hessian_clm,
      add_zero,jet_hessian_sub_smooth hA hP] at hmat
    change (-(hessian (peanoPolynomial (W y) y l B (-rho)) y-hessian P y : Sym n) : Mat n).PosSemidef at hmat
    simp only [AddSubgroup.coe_sub] at hmat
    rw [peanoPolynomial_hessian_coe (W y) y l B hW.1 (-rho) y] at hmat
    convert! hmat using 1
    module
  have hc : Continuous (fun rho : ℝ =>
      (hessian P y : Mat n)-(jointHessian B : Mat n)+(2*rho) • (1 : Mat n)) := by fun_prop
  have ht : Tendsto (fun rho : ℝ =>
      (hessian P y : Mat n)-(jointHessian B : Mat n)+(2*rho) • (1 : Mat n))
      (𝓝[>] 0) (𝓝 ((hessian P y : Mat n)-(jointHessian B : Mat n))) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply Matrix.posSemidef_is_closed.mem_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with rho hrho
  exact hRho rho hrho

theorem jet_convex_symmetric_quadratic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ x y, B x y=B y x)
    (hNonneg : ∀ x, 0≤B x x) (c : ℝ) (l : E →L[ℝ] ℝ) :
    ConvexOn ℝ univ (fun x => c+l x+(1/2 : ℝ)*B x x) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  have hbEq : b=1-a := by linarith
  have hAB : 0≤a*b := mul_nonneg ha hb
  have hQuad := mul_nonneg (by positivity : 0≤a*b/2) (hNonneg (x-y))
  have hIdentity :
      a*(c+l x+(1/2 : ℝ)*B x x)+b*(c+l y+(1/2 : ℝ)*B y y)-
        (c+l (a • x+b • y)+(1/2 : ℝ)*B (a • x+b • y) (a • x+b • y)) =
        (a*b/2)*B (x-y) (x-y) := by
    simp only [map_add,map_smul,map_sub,add_apply,sub_apply,smul_apply,smul_eq_mul]
    rw [hB y x,hbEq]
    ring
  change c+l (a • x+b • y)+(1/2 : ℝ)*B (a • x+b • y) (a • x+b • y) ≤
    a*(c+l x+(1/2 : ℝ)*B x x)+b*(c+l y+(1/2 : ℝ)*B y y)
  linarith only [hIdentity,hQuad]

end Yau.LeafProofs.L05Aux
