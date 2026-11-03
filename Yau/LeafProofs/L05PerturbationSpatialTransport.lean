import Yau.LeafProofs.L05PerturbationTimeTransport

open Set Metric Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_second_affine {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (d : F)
    {f : F → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f (L x+d)) :
    fderiv ℝ (fderiv ℝ (fun y => f (L y+d))) x=
      (fderiv ℝ (fderiv ℝ f) (L x+d)).bilinearComp L L := by
  have ha : HasFDerivAt (fun y => L y+d) L x := L.hasFDerivAt.add_const d
  have hg := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hd := (hg.comp x ha).clm_comp (hasFDerivAt_const L x)
  have hn : ∀ᶠ y in 𝓝 (L x+d), DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  have he : fderiv ℝ (fun y => f (L y+d)) =ᶠ[𝓝 x]
      fun y => (fderiv ℝ f (L y+d)).comp L := by
    filter_upwards [ha.continuousAt.tendsto hn] with y hy
    exact (hy.hasFDerivAt.comp y (L.hasFDerivAt.add_const d)).fderiv
  rw [he.fderiv_eq]
  have hfd := hd.fderiv
  simp only [Function.comp_def] at hfd
  rw [hfd]
  ext v w
  simp [ContinuousLinearMap.bilinearComp_apply]

theorem perturb_second_mul_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (a c : ℝ) :
    fderiv ℝ (fderiv ℝ (fun y => a*(f y-c))) x=a • fderiv ℝ (fderiv ℝ f) x := by
  have he : fderiv ℝ (fun y => a*(f y-c)) =ᶠ[𝓝 x] fun y => a • fderiv ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    rw [fderiv_const_mul ((hy.differentiableAt (by norm_num)).sub_const c) a,
      fderiv_sub_const]
  rw [he.fderiv_eq]
  exact fderiv_fun_const_smul
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) a

theorem perturb_space_second_scale {n : ℕ} (c : Space n) (r : ℝ)
    {f : Space n → ℝ} {x : Space n} (hf : ContDiffAt ℝ 2 f (c+r • x)) :
    fderiv ℝ (fderiv ℝ (fun y => f (c+r • y))) x=
      r^2 • fderiv ℝ (fderiv ℝ f) (c+r • x) := by
  let L : Space n →L[ℝ] Space n := r • ContinuousLinearMap.id ℝ (Space n)
  have hs : ContDiffAt ℝ 2 f (L x+c) := by simpa only [L,smul_apply,ContinuousLinearMap.id_apply,add_comm] using hf
  have hh := perturb_second_affine L c hs
  have he : (fun y => f (L y+c))=(fun y => f (c+r • y)) := by
    funext y
    simp only [L,smul_apply,ContinuousLinearMap.id_apply,add_comm]
  rw [he] at hh
  rw [show L x+c=c+r • x by simp [L,add_comm]] at hh
  rw [hh]
  ext v w
  simp [L,ContinuousLinearMap.bilinearComp_apply,pow_two,mul_assoc]


theorem perturb_normalize_spatial_contDiffAt {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) (z : Point n) {r N q0 : ℝ} (hr : 0<r)
    (hbuf : perturbClosed z.1 r z.2 ⊆ backward 1)
    {p : Point n} (hp : p ∈ backward 1) :
    ContDiffAt ℝ 2 (fun x => perturbNormalize u z r N q0 (x,p.2)) p.1 := by
  have hq := perturb_center_mem_original hr hbuf hp
  have hf := hu.2.2.2.2.1 _ hq
  have hx : ContDiffAt ℝ 2 (fun x : Space n => z.1+r • x) p.1 :=
    contDiffAt_const.add (contDiffAt_id.const_smul r)
  have hraw := hf.comp p.1 hx
  have h0 : ContDiffAt ℝ 2 (fun _ : Space n => u z) p.1 := contDiffAt_const
  have h1 : ContDiffAt ℝ 2 (fun _ : Space n => r^2*q0*p.2) p.1 := contDiffAt_const
  simpa only [perturbNormalize,perturbCenter,Function.comp_def] using ((hraw.sub h0).sub h1).div_const N

theorem perturb_normalize_spatialD {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) (z : Point n) {r N q0 : ℝ} (hr : 0<r)
    (hbuf : perturbClosed z.1 r z.2 ⊆ backward 1)
    {p : Point n} (hp : p ∈ backward 1) :
    spatialD (perturbNormalize u z r N q0) p=
      (r/N) • spatialD u (perturbCenter z r p) := by
  let L : Space n →L[ℝ] Space n := r • ContinuousLinearMap.id ℝ (Space n)
  have ha : HasFDerivAt (fun x : Space n => z.1+r • x) L p.1 := by
    convert! L.hasFDerivAt.const_add z.1 using 1
  have hf := (hu.2.2.2.2.1 _ (perturb_center_mem_original hr hbuf hp)).differentiableAt (by norm_num)
  have hh := (((hf.hasFDerivAt.comp p.1 ha).sub_const (u z)).sub_const
    (r^2*q0*p.2)).const_mul N⁻¹
  have he := hh.fderiv
  simp only [Function.comp_def,perturbCenter] at he
  change fderiv ℝ (fun x => perturbNormalize u z r N q0 (x,p.2)) p.1 = _
  have hefun : (fun x => perturbNormalize u z r N q0 (x,p.2))=
      fun x => N⁻¹*(u (z.1+r • x,z.2+r^2*p.2)-u z-r^2*q0*p.2) := by
    funext x
    dsimp only [perturbNormalize,perturbCenter]
    ring
  rw [hefun,he]
  ext v
  simp [spatialD,perturbCenter,L,div_eq_mul_inv,mul_comm,mul_left_comm]
  ring

theorem perturb_normalize_spatialDD {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) (z : Point n) {r N q0 : ℝ} (hr : 0<r)
    (hbuf : perturbClosed z.1 r z.2 ⊆ backward 1)
    {p : Point n} (hp : p ∈ backward 1) :
    spatialDD (perturbNormalize u z r N q0) p=
      (r^2/N) • spatialDD u (perturbCenter z r p) := by
  have hf := hu.2.2.2.2.1 _ (perturb_center_mem_original hr hbuf hp)
  have hx : ContDiffAt ℝ 2 (fun x : Space n => z.1+r • x) p.1 :=
    contDiffAt_const.add (contDiffAt_id.const_smul r)
  have hh := hf.comp p.1 hx
  dsimp only [Function.comp_def,perturbCenter] at hh hf
  have he : (fun x => perturbNormalize u z r N q0 (x,p.2))=
      (fun x => N⁻¹*(u (z.1+r • x,z.2+r^2*p.2)-(u z+r^2*q0*p.2))) := by
    funext x
    dsimp only [perturbNormalize,perturbCenter]
    ring
  change fderiv ℝ (fderiv ℝ (fun x => perturbNormalize u z r N q0 (x,p.2))) p.1 = _
  rw [he,perturb_second_mul_sub hh,perturb_space_second_scale z.1 r hf]
  simp only [smul_smul]
  congr 1
  rw [div_eq_mul_inv,mul_comm]

end Yau.LeafProofs.L05Aux
