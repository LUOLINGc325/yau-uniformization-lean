import Yau.LeafProofs.L22LeviCalculus
import Yau.LeafProofs.L22Second
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

noncomputable section
open Filter InnerProductSpace
open scoped Topology

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L22Aux

def planarTrace (f : ℂ → ℝ) (a : ℂ) : ℝ :=
  fderiv ℝ (fderiv ℝ f) a 1 1 + fderiv ℝ (fderiv ℝ f) a Complex.I Complex.I

theorem planarTrace_add (f g : ℂ → ℝ) (a : ℂ)
    (hf : ContDiffAt ℝ 2 f a) (hg : ContDiffAt ℝ 2 g a) :
    planarTrace (fun z => f z+g z) a = planarTrace f a+planarTrace g a := by
  simp only [planarTrace, secondFDeriv_add hf hg]
  ring

theorem planarTrace_const_mul (f : ℂ → ℝ) (a : ℂ)
    (hf : ContDiffAt ℝ 2 f a) (c : ℝ) :
    planarTrace (fun z => c*f z) a = c*planarTrace f a := by
  simp only [planarTrace, secondFDeriv_const_mul hf]
  ring

theorem planarTrace_const (c : ℝ) (a : ℂ) : planarTrace (fun _ => c) a = 0 := by
  simp [planarTrace]

set_option backward.isDefEq.respectTransparency false in
theorem planarTrace_norm_sq (a : ℂ) : planarTrace (fun z : ℂ => ‖z‖^2) a = 4 := by
  have HD : fderiv ℝ (fderiv ℝ (fun z : ℂ => ‖z‖^2)) a =
      2 • innerSL ℝ (E := ℂ) := by
    rw [fderiv_norm_sq]
    exact (2 • innerSL ℝ (E := ℂ)).fderiv
  simp only [planarTrace,HD,two_smul,add_apply]
  have h1 : (innerSL ℝ (E := ℂ)) (1 : ℂ) 1 = 1 := by
    change inner ℝ (1 : ℂ) 1 = 1
    rw [real_inner_self_eq_norm_sq]
    norm_num
  have hI : (innerSL ℝ (E := ℂ)) Complex.I Complex.I = 1 := by
    change inner ℝ Complex.I Complex.I = 1
    rw [real_inner_self_eq_norm_sq]
    norm_num
  rw [h1,hI]
  norm_num

theorem planarTrace_harmonic {f : ℂ → ℝ} {a : ℂ} (hf : HarmonicAt f a) :
    planarTrace f a = 0 := by
  have H := hf.2.self_of_nhds
  rw [laplacian_eq_iteratedFDeriv_complexPlane] at H
  simpa only [planarTrace, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply] using H

theorem planarTrace_nonneg_of_localMin {f : ℂ → ℝ} {a : ℂ}
    (hf : ContDiffAt ℝ 2 f a) (hmin : IsLocalMin f a) : 0 ≤ planarTrace f a :=
  add_nonneg (hessian_nonneg_of_localMin hf hmin 1)
    (hessian_nonneg_of_localMin hf hmin Complex.I)

theorem planarTrace_complexAffine {n : ℕ} (f : ComplexVector n → ℝ)
    (z w : ComplexVector n) (a : ℂ) (hf : ContDiffAt ℝ 2 f (z+a • w)) :
    planarTrace (fun ζ : ℂ => f (z+ζ • w)) a =
      4*complexLeviQuadratic f (z+a • w) w := by
  let L : ℂ →L[ℝ] ComplexVector n :=
    ((ContinuousLinearMap.id ℂ ℂ).smulRight w).restrictScalars ℝ
  have hF (b : ℂ) : HasFDerivAt (fun ζ : ℂ => z+ζ • w) L b := by
    simpa only [L, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.coe_restrictScalars'] using L.hasFDerivAt.const_add z
  have hD : fderiv ℝ (fun ζ : ℂ => z+ζ • w) = fun _ => L := by
    funext b
    exact (hF b).fderiv
  have hF2 : ContDiffAt ℝ 2 (fun ζ : ℂ => z+ζ • w) a :=
    contDiffAt_const.add L.contDiff.contDiffAt
  have hDD : fderiv ℝ (fun _ : ℂ => L) a = 0 :=
    (hasFDerivAt_const L a).fderiv
  unfold planarTrace
  change fderiv ℝ (fderiv ℝ (f ∘ fun ζ : ℂ => z+ζ • w)) a 1 1 +
    fderiv ℝ (fderiv ℝ (f ∘ fun ζ : ℂ => z+ζ • w)) a Complex.I Complex.I = _
  rw [L18Aux.secondFDeriv_comp hF2 hf, L18Aux.secondFDeriv_comp hF2 hf]
  simp only [hD,hDD,ContinuousLinearMap.zero_apply,map_zero,add_zero,
    L,ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,one_smul]
  unfold complexLeviQuadratic
  ring

end Yau.NodeProofs.P02Aux
