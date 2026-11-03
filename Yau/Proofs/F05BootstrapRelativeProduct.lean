import Yau.Proofs.F05BootstrapDefinitions

/-! Actual within-set product rules through the spatial Hessian. They
differentiate each spatial slice twice and require no joint mixed derivative. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_second_fderivWithin_mul_apply {X : Set (Space n)}
    (hX : UniqueDiffOn ℝ X) {f g : Space n → ℝ}
    (hf : ContDiffOn ℝ 2 f X) (hg : ContDiffOn ℝ 2 g X)
    {x : Space n} (hx : x ∈ X) (v w : Space n) :
    fderivWithin ℝ (fderivWithin ℝ (fun y => f y*g y) X) X x v w =
      f x*fderivWithin ℝ (fderivWithin ℝ g X) X x v w+
        fderivWithin ℝ f X x v*fderivWithin ℝ g X x w+
        fderivWithin ℝ f X x w*fderivWithin ℝ g X x v+
        g x*fderivWithin ℝ (fderivWithin ℝ f X) X x v w := by
  have hf1 := hf.differentiableOn (by norm_num) x hx
  have hg1 := hg.differentiableOn (by norm_num) x hx
  have hf2 := (hf.fderivWithin hX (m := 1) (by norm_num)).differentiableOn (by norm_num) x hx
  have hg2 := (hg.fderivWithin hX (m := 1) (by norm_num)).differentiableOn (by norm_num) x hx
  have hprod2 := ((hf.mul hg).fderivWithin hX (m := 1)
    (by norm_num)).differentiableOn (by norm_num) x hx
  have hleft : fderivWithin ℝ (fun y => fderivWithin ℝ (fun z => f z*g z) X y w) X x v =
      fderivWithin ℝ (fderivWithin ℝ (fun y => f y*g y) X) X x v w := by
    rw [fderivWithin_clm_apply (hX x hx) hprod2 (differentiableWithinAt_const w)]
    simp
  have hEq : EqOn (fun y => fderivWithin ℝ (fun z => f z*g z) X y w)
      (fun y => f y*fderivWithin ℝ g X y w+g y*fderivWithin ℝ f X y w) X := by
    intro y hy
    change fderivWithin ℝ (fun z => f z*g z) X y w =
      f y*fderivWithin ℝ g X y w+g y*fderivWithin ℝ f X y w
    rw [fderivWithin_fun_mul (hX y hy)
      (hf.differentiableOn (by norm_num) y hy) (hg.differentiableOn (by norm_num) y hy)]
    simp
  have hdg : DifferentiableWithinAt ℝ (fun y => fderivWithin ℝ g X y w) X x :=
    hg2.clm_apply (differentiableWithinAt_const w)
  have hdf : DifferentiableWithinAt ℝ (fun y => fderivWithin ℝ f X y w) X x :=
    hf2.clm_apply (differentiableWithinAt_const w)
  rw [← hleft,fderivWithin_congr hEq (hEq hx),
    fderivWithin_fun_add (hX x hx) (hf1.fun_mul hdg) (hg1.fun_mul hdf),
    fderivWithin_fun_mul (hX x hx) hf1 hdg,fderivWithin_fun_mul (hX x hx) hg1 hdf,
    fderivWithin_clm_apply (hX x hx) hg2 (differentiableWithinAt_const w),
    fderivWithin_clm_apply (hX x hx) hf2 (differentiableWithinAt_const w)]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    fderivWithin_const_apply,ContinuousLinearMap.comp_zero,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.zero_apply,mul_zero,add_zero,zero_add]
  ring

theorem F05_second_fderivWithin_mul {X : Set (Space n)}
    (hX : UniqueDiffOn ℝ X) {f g : Space n → ℝ}
    (hf : ContDiffOn ℝ 2 f X) (hg : ContDiffOn ℝ 2 g X) {x : Space n} (hx : x ∈ X) :
    fderivWithin ℝ (fderivWithin ℝ (fun y => f y*g y) X) X x =
      f x • fderivWithin ℝ (fderivWithin ℝ g X) X x+
        (fderivWithin ℝ f X x).smulRight (fderivWithin ℝ g X x)+
        (fderivWithin ℝ g X x).smulRight (fderivWithin ℝ f X x)+
        g x • fderivWithin ℝ (fderivWithin ℝ f X) X x := by
  ext v w
  rw [F05_second_fderivWithin_mul_apply hX hf hg hx]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

end Yau.Proofs.F05Aux
