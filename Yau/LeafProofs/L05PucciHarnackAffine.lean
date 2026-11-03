import Yau.LeafProofs.L05PucciHarnackScaling

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackAffineLinear (n : ℕ) (R T : ℝ) : Point n →L[ℝ] Point n :=
  (R • ContinuousLinearMap.fst ℝ (Space n) ℝ).prod (T • ContinuousLinearMap.snd ℝ (Space n) ℝ)

@[simp] theorem harnack_affineLinear_apply {n : ℕ} (R T : ℝ) (z : Point n) :
    harnackAffineLinear n R T z=(R • z.1,T*z.2) := rfl

def harnackAffine {n : ℕ} (c : Space n) (R a T : ℝ) (z : Point n) : Point n :=
  harnackAffineLinear n R T z+(c,a+T)

def harnackAffineInv {n : ℕ} (c : Space n) (R a T : ℝ) (p : Point n) : Point n :=
  harnackAffineLinear n R⁻¹ T⁻¹ p-harnackAffineLinear n R⁻¹ T⁻¹ (c,a+T)

theorem harnack_affine_apply {n : ℕ} (c : Space n) (R a T : ℝ) (z : Point n) :
    harnackAffine c R a T z=(c+R • z.1,a+T*(z.2+1)) := by
  apply Prod.ext
  · exact add_comm _ _
  · change T*z.2+(a+T)=a+T*(z.2+1)
    ring

theorem harnack_affineLinear_comp {n : ℕ} (R T r t : ℝ) (z : Point n) :
    harnackAffineLinear n R T (harnackAffineLinear n r t z)=harnackAffineLinear n (R*r) (T*t) z := by
  apply Prod.ext
  · change R • (r • z.1)=(R*r) • z.1
    exact smul_smul _ _ _
  · change T*(t*z.2)=(T*t)*z.2
    ring

theorem harnack_affineLinear_one {n : ℕ} (z : Point n) : harnackAffineLinear n 1 1 z=z := by
  simp only [harnack_affineLinear_apply,one_smul,one_mul,Prod.eta]

theorem harnack_affine_inv_apply {n : ℕ} {c : Space n} {R a T : ℝ}
    (hR : R≠0) (hT : T≠0) (z : Point n) : harnackAffineInv c R a T (harnackAffine c R a T z)=z := by
  unfold harnackAffineInv harnackAffine
  rw [map_add,add_sub_cancel_right,harnack_affineLinear_comp,inv_mul_cancel₀ hR,inv_mul_cancel₀ hT,
    harnack_affineLinear_one]

theorem harnack_affine_apply_inv {n : ℕ} {c : Space n} {R a T : ℝ}
    (hR : R≠0) (hT : T≠0) (z : Point n) : harnackAffine c R a T (harnackAffineInv c R a T z)=z := by
  unfold harnackAffineInv harnackAffine
  rw [map_sub,harnack_affineLinear_comp,harnack_affineLinear_comp,mul_inv_cancel₀ hR,mul_inv_cancel₀ hT,
    harnack_affineLinear_one,harnack_affineLinear_one,sub_add_cancel]

theorem harnack_affine_hasFDerivAt {n : ℕ} (c : Space n) (R a T : ℝ) (z : Point n) :
    HasFDerivAt (harnackAffine c R a T) (harnackAffineLinear n R T) z :=
  (harnackAffineLinear n R T).hasFDerivAt.add_const _

theorem harnack_affineInv_hasFDerivAt {n : ℕ} (c : Space n) (R a T : ℝ) (z : Point n) :
    HasFDerivAt (harnackAffineInv c R a T) (harnackAffineLinear n R⁻¹ T⁻¹) z :=
  (harnackAffineLinear n R⁻¹ T⁻¹).hasFDerivAt.sub_const _

theorem harnack_affine_contDiff {n : ℕ} (c : Space n) (R a T : ℝ) :
    ContDiff ℝ ∞ (harnackAffine c R a T) :=
  (harnackAffineLinear n R T).contDiff.add contDiff_const

theorem harnack_affineInv_contDiff {n : ℕ} (c : Space n) (R a T : ℝ) :
    ContDiff ℝ ∞ (harnackAffineInv c R a T) :=
  (harnackAffineLinear n R⁻¹ T⁻¹).contDiff.sub contDiff_const

theorem harnack_affineLinear_spatial {n : ℕ} (R T : ℝ) (v : Space n) :
    harnackAffineLinear n R T (v,0)=R • ((v,0) : Point n) := by
  simp only [harnack_affineLinear_apply,mul_zero,Prod.smul_mk,smul_zero]

theorem harnack_affineLinear_temporal {n : ℕ} (R T : ℝ) :
    harnackAffineLinear n R T ((0,1) : Point n)=T • ((0,1) : Point n) := by
  simp only [harnack_affineLinear_apply,smul_zero,mul_one,Prod.smul_mk,smul_eq_mul,mul_one]

theorem harnack_second_affine_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (d : F) {phi : F → ℝ} {z : E}
    (hphi : ContDiffAt ℝ 2 phi (L z+d)) :
    fderiv ℝ (fderiv ℝ (fun y => phi (L y+d))) z=
      (fderiv ℝ (fderiv ℝ phi) (L z+d)).bilinearComp L L := by
  have hAff : HasFDerivAt (fun y => L y+d) L z := L.hasFDerivAt.add_const d
  have hGrad := ((hphi.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hGradPull := (hGrad.comp z hAff).clm_comp (hasFDerivAt_const L z)
  have hNear : ∀ᶠ y in 𝓝 (L z+d), DifferentiableAt ℝ phi y := by
    filter_upwards [hphi.eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hEq : (fun y => fderiv ℝ (fun x => phi (L x+d)) y) =ᶠ[𝓝 z]
      (fun y => (fderiv ℝ phi (L y+d)).comp L) := by
    filter_upwards [hAff.continuousAt.tendsto hNear] with y hy
    convert! (hy.hasFDerivAt.comp y (L.hasFDerivAt.add_const d)).fderiv using 1
  rw [hEq.fderiv_eq]
  have hF := hGradPull.fderiv
  simp only [Function.comp_def] at hF
  rw [hF]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp [ContinuousLinearMap.bilinearComp_apply]

theorem harnack_affine_pullback_timeD {n : ℕ} (R T : ℝ) (d z : Point n) {phi : Point n → ℝ}
    (hphi : ContDiffAt ℝ 2 phi (harnackAffineLinear n R T z+d)) :
    timeD univ (fun y => phi (harnackAffineLinear n R T y+d)) z=
      T*timeD univ phi (harnackAffineLinear n R T z+d) := by
  have hd := (hphi.differentiableAt (by norm_num)).hasFDerivAt.comp z
    ((harnackAffineLinear n R T).hasFDerivAt.add_const d)
  have hd' : HasFDerivAt (fun y => phi (harnackAffineLinear n R T y+d))
      ((fderiv ℝ phi (harnackAffineLinear n R T z+d)).comp (harnackAffineLinear n R T)) z := by
    convert! hd using 1
  rw [timeD_univ_eq_joint hd'.differentiableAt,hd'.fderiv]
  simp only [ContinuousLinearMap.comp_apply,harnack_affineLinear_temporal,map_smul,smul_eq_mul]
  rw [← timeD_univ_eq_joint (hphi.differentiableAt (by norm_num))]

theorem harnack_affine_pullback_hessian {n : ℕ} (R T : ℝ) (d z : Point n) {phi : Point n → ℝ}
    (hphi : ContDiffAt ℝ 2 phi (harnackAffineLinear n R T z+d)) :
    hessian (fun y => phi (harnackAffineLinear n R T y+d)) z=
      R^2 • hessian phi (harnackAffineLinear n R T z+d) := by
  have hComp : ContDiffAt ℝ 2 (fun y => phi (harnackAffineLinear n R T y+d)) z :=
    hphi.comp z ((harnackAffineLinear n R T).contDiff.contDiffAt.add contDiffAt_const)
  rw [jet_hessian_eq_joint_at hComp,jet_hessian_eq_joint_at hphi,
    harnack_second_affine_comp _ _ hphi]
  let B := fderiv ℝ (fderiv ℝ phi) (harnackAffineLinear n R T z+d)
  have hH : jointHessian (B.bilinearComp (harnackAffineLinear n R T) (harnackAffineLinear n R T))=
      jointHessian (R^2 • B) := by
    unfold jointHessian
    apply congrArg (selfAdjointPart ℝ)
    funext i j
    simp only [ContinuousLinearMap.bilinearComp_apply,harnack_affineLinear_spatial,
      map_smul,smul_apply,smul_eq_mul]
    ring
  rw [hH,jet_jointHessian_smul]

end Yau.LeafProofs.L05Aux
