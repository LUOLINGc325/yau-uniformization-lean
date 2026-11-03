import Yau.Proofs.V03LeviLocality

/-! Native second-derivative calculus and holomorphic pullback naturality
for the real part of the actual nested Wirtinger derivative. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

theorem fderiv_wirtBar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {z : E} (hf : DifferentiableAt ℝ (fderiv ℝ f) z) (v w : E) :
    fderiv ℝ (fun y => wirtBar f y v) z w =
      (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ f) z w v +
        Complex.I * fderiv ℝ (fderiv ℝ f) z w (Complex.I • v)) := by
  have hv := hf.clm_apply (differentiableAt_const v)
  have hIv := hf.clm_apply (differentiableAt_const (Complex.I • v))
  simp only [wirtBar]
  rw [fderiv_const_mul (hv.fun_add (hIv.const_mul Complex.I)),
    fderiv_fun_add hv (hIv.const_mul Complex.I), fderiv_const_mul hIv,
    fderiv_clm_apply hf (differentiableAt_const v),
    fderiv_clm_apply hf (differentiableAt_const (Complex.I • v))]
  simp
  ring

theorem mixedWirt_eq_secondFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {z : E} (hf : DifferentiableAt ℝ (fderiv ℝ f) z) (v w : E) :
    wirt (fun y => wirtBar f y v) z w =
      (1 / 4 : ℂ) * (fderiv ℝ (fderiv ℝ f) z w v +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • w) (Complex.I • v) +
        Complex.I * (fderiv ℝ (fderiv ℝ f) z w (Complex.I • v) -
          fderiv ℝ (fderiv ℝ f) z (Complex.I • w) v)) := by
  rw [wirt, fderiv_wirtBar hf, fderiv_wirtBar hf]
  linear_combination -(1 / 4 : ℂ) *
    fderiv ℝ (fderiv ℝ f) z (Complex.I • w) (Complex.I • v) * Complex.I_sq

theorem secondFDeriv_ofReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => (f y : ℂ))) z w v =
      (fderiv ℝ (fderiv ℝ f) z w v : ℂ) := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hF : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  have hdF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heq : (fun y => fderiv ℝ (fun y' => (f y' : ℂ)) y v) =ᶠ[𝓝 z]
      (fun y => (fderiv ℝ f y v : ℂ)) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    have hd := hy.differentiableAt (by norm_num)
    change fderiv ℝ (Complex.ofRealCLM ∘ f) y v = _
    rw [fderiv_comp y Complex.ofRealCLM.differentiableAt hd]
    simp
  have h := congrArg (fun L : E →L[ℝ] ℂ => L w) heq.fderiv_eq
  rw [fderiv_clm_apply hdF (differentiableAt_const v)] at h
  change _ = fderiv ℝ (Complex.ofRealCLM ∘ (fun y => fderiv ℝ f y v)) z w at h
  rw [fderiv_comp z Complex.ofRealCLM.differentiableAt
    (hdf.clm_apply (differentiableAt_const v)),
    fderiv_clm_apply hdf (differentiableAt_const v)] at h
  simpa using h

theorem mixedWirt_real_diagonal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v : E) :
    (wirt (fun y => wirtBar (fun y' => (f y' : ℂ)) y v) z v).re =
      (1 / 4 : ℝ) * (fderiv ℝ (fderiv ℝ f) z v v +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • v) (Complex.I • v)) := by
  have hF : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  rw [mixedWirt_eq_secondFDeriv
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)]
  simp only [secondFDeriv_ofReal hf, Complex.mul_re, Complex.add_re, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.add_im, Complex.sub_im, mul_zero, zero_mul, add_zero, sub_zero]
  norm_num

theorem secondFDeriv_comp {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {u : F → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hu : ContDiffAt ℝ 2 u (f x)) (v w : E) :
    fderiv ℝ (fderiv ℝ (u ∘ f)) x v w =
      fderiv ℝ (fderiv ℝ u) (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) +
        fderiv ℝ u (f x) (fderiv ℝ (fderiv ℝ f) x v w) := by
  have hfd := hf.differentiableAt (by norm_num)
  have hfdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hudd := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hunear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 u (f y) :=
    hf.continuousAt.eventually (hu.eventually (by norm_num))
  have heq : fderiv ℝ (u ∘ f) =ᶠ[𝓝 x]
      (fun y => (fderiv ℝ u (f y)).comp (fderiv ℝ f y)) := by
    filter_upwards [hf.eventually (by norm_num), hunear] with y hfy huy
    exact fderiv_comp y (huy.differentiableAt (by norm_num)) (hfy.differentiableAt (by norm_num))
  have hcomp : DifferentiableAt ℝ (fun y => fderiv ℝ u (f y)) x := hudd.comp x hfd
  have hdc : fderiv ℝ (fun y => fderiv ℝ u (f y)) x =
      (fderiv ℝ (fderiv ℝ u) (f x)).comp (fderiv ℝ f x) :=
    fderiv_comp (g := fderiv ℝ u) x hudd hfd
  rw [heq.fderiv_eq, fderiv_clm_comp hcomp hfdd, hdc]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
  ring

theorem secondFDeriv_restrict_complex {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {z : E} (hf : ContDiffAt ℂ 2 f z) (v w : E) :
    fderiv ℝ (fderiv ℝ f) z v w = fderiv ℂ (fderiv ℂ f) z v w := by
  have h := congrArg (fun A => A ![v, w]) (hf.restrictScalars_iteratedFDeriv (𝕜 := ℝ))
  simpa only [Function.comp_apply, ContinuousMultilinearMap.coe_restrictScalars,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h.symm

theorem secondFDeriv_complex_I_I {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {z : E} (hf : ContDiffAt ℂ 2 f z) (v w : E) :
    fderiv ℝ (fderiv ℝ f) z (Complex.I • v) (Complex.I • w) =
      -fderiv ℝ (fderiv ℝ f) z v w := by
  rw [secondFDeriv_restrict_complex hf, secondFDeriv_restrict_complex hf]
  simp only [map_smul, smul_apply, smul_smul, Complex.I_mul_I, neg_one_smul]

theorem mixedWirt_holomorphic_comp_re {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T : E → F} {f : F → ℝ} {z : E} (hT : ContDiffAt ℂ 2 T z)
    (hf : ContDiffAt ℝ 2 f (T z)) (v : E) :
    (wirt (fun y => wirtBar (fun y' => (f (T y') : ℂ)) y v) z v).re =
      (wirt (fun y => wirtBar (fun y' => (f y' : ℂ)) y
        (fderiv ℂ T z v)) (T z) (fderiv ℂ T z v)).re := by
  have hd := hT.differentiableAt (by norm_num)
  have hreal (w : E) : fderiv ℝ T z w = fderiv ℂ T z w := by
    exact congrArg (fun L : E →L[ℝ] F => L w) (hd.fderiv_restrictScalars ℝ)
  have hTR := hT.restrict_scalars ℝ
  change (wirt (fun y => wirtBar (fun y' => ((f ∘ T) y' : ℂ)) y v) z v).re = _
  rw [mixedWirt_real_diagonal (hf.comp z hTR), mixedWirt_real_diagonal hf]
  simp only [secondFDeriv_comp hTR hf, secondFDeriv_complex_I_I hT, map_neg,
    hreal, map_smul]
  ring

end Yau.Blueprint.V03Proof
