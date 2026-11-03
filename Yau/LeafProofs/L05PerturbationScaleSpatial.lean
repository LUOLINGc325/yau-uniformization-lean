import Yau.LeafProofs.L05PerturbationScaleTime

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_scaleValue_spatial_contDiffAt {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) {r N : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {p : Point n} (hp : p∈backward 1) :
    ContDiffAt ℝ 2 (fun x => perturbScaleValue u r N (x,p.2)) p.1 := by
  have hf := hu.2.2.2.2.1 _ (perturb_scale_back_mem hr hr1 hp)
  change ContDiffAt ℝ 2 (fun y => u (y,r^2*p.2)) (r • p.1) at hf
  have hh := (hf.comp p.1 (contDiffAt_id.const_smul r)).div_const N
  simpa only [perturbScaleValue,perturbScale,Function.comp_def] using hh

theorem perturb_scaleValue_spatialD {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) {r N : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {p : Point n} (hp : p∈backward 1) :
    spatialD (perturbScaleValue u r N) p=(r/N) • spatialD u (perturbScale r p) := by
  let L : Space n →L[ℝ] Space n := r • ContinuousLinearMap.id ℝ (Space n)
  have hLine : HasFDerivAt (fun x : Space n => r • x) L p.1 := L.hasFDerivAt
  have hf := (hu.2.2.2.2.1 _ (perturb_scale_back_mem hr hr1 hp)).differentiableAt (by norm_num)
  change DifferentiableAt ℝ (fun y => u (y,r^2*p.2)) (r • p.1) at hf
  have hh := (hf.hasFDerivAt.comp p.1 hLine).const_mul N⁻¹
  have he := hh.fderiv
  simp only [Function.comp_def] at he
  have hefun : (fun y => perturbScaleValue u r N (y,p.2))=
      (fun y => N⁻¹*u (r • y,r^2*p.2)) := by
    funext y
    dsimp only [perturbScaleValue,perturbScale]
    ring
  change fderiv ℝ (fun y => perturbScaleValue u r N (y,p.2)) p.1 = _
  rw [hefun,he]
  ext v
  simp [spatialD,perturbScale,L,div_eq_mul_inv,mul_comm,mul_left_comm]
  ring

theorem perturb_scaleValue_spatialDD {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) {r N : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {p : Point n} (hp : p∈backward 1) :
    spatialDD (perturbScaleValue u r N) p=(r^2/N) • spatialDD u (perturbScale r p) := by
  have hf := hu.2.2.2.2.1 _ (perturb_scale_back_mem hr hr1 hp)
  change ContDiffAt ℝ 2 (fun y => u (y,r^2*p.2)) (r • p.1) at hf
  have hf' : ContDiffAt ℝ 2 (fun y => u (y,r^2*p.2)) ((0 : Space n)+r • p.1) := by
    simpa only [zero_add] using hf
  have hx : ContDiffAt ℝ 2 (fun y : Space n => (0 : Space n)+r • y) p.1 :=
    contDiffAt_const.add (contDiffAt_id.const_smul r)
  have hh := hf'.comp p.1 hx
  simp only [Function.comp_def] at hh
  have hefun : (fun y => perturbScaleValue u r N (y,p.2))=
      (fun y => N⁻¹*(u ((0 : Space n)+r • y,r^2*p.2)-0)) := by
    funext y
    dsimp only [perturbScaleValue,perturbScale]
    rw [zero_add,sub_zero]
    ring
  change fderiv ℝ (fderiv ℝ (fun y => perturbScaleValue u r N (y,p.2))) p.1 = _
  rw [hefun,perturb_second_mul_sub hh,perturb_space_second_scale (0 : Space n) r hf']
  simp only [zero_add,smul_smul]
  congr 1
  rw [div_eq_mul_inv,mul_comm]

end Yau.LeafProofs.L05Aux
