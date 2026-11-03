import Yau.Proofs.V03ThirdDerivative

/-! The actual real two-form of i∂∂bar f is closed. Both its coefficient
formula and its closure are derived from the original Fréchet Wirtinger
operators and native third-derivative symmetry. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def leviTwoForm (f : E → ℝ) (z v w : E) : ℝ :=
  2 * (wirt (fun y => wirtBar (fun x => (f x : ℂ)) y v) z w).im

theorem leviTwoForm_eq_secondFDeriv {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    leviTwoForm f z v w = (1 / 2 : ℝ) *
      (fderiv ℝ (fderiv ℝ f) z w (Complex.I • v) -
        fderiv ℝ (fderiv ℝ f) z (Complex.I • w) v) := by
  have hF : ContDiffAt ℝ 2 (fun x => (f x : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  rw [leviTwoForm, mixedWirt_eq_secondFDeriv
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)]
  simp only [secondFDeriv_ofReal hf, Complex.mul_im, Complex.mul_re, Complex.add_im,
    Complex.add_re, Complex.sub_im, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, zero_add, sub_zero]
  norm_num <;> ring

theorem fderiv_leviTwoForm {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 3 f z) (u v w : E) :
    fderiv ℝ (fun y => leviTwoForm f y v w) z u = (1 / 2 : ℝ) *
      (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z u w (Complex.I • v) -
        fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z u (Complex.I • w) v) := by
  have hnear : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 f y :=
    (hf.of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)).eventually (by norm_num)
  have heq : (fun y => leviTwoForm f y v w) =ᶠ[𝓝 z]
      (fun y => (1 / 2 : ℝ) * (fderiv ℝ (fderiv ℝ f) y w (Complex.I • v) -
        fderiv ℝ (fderiv ℝ f) y (Complex.I • w) v)) := by
    filter_upwards [hnear] with y hy
    exact leviTwoForm_eq_secondFDeriv hy v w
  have hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) z :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero
  have hA := (hH.clm_apply (differentiableAt_const w)).clm_apply
    (differentiableAt_const (Complex.I • v))
  have hB := (hH.clm_apply (differentiableAt_const (Complex.I • w))).clm_apply
    (differentiableAt_const v)
  rw [heq.fderiv_eq, fderiv_const_mul (hA.fun_sub hB), fderiv_fun_sub hA hB]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.sub_apply,
    fderiv_secondFDeriv_apply hH]

theorem leviTwoForm_closed {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 3 f z) (u v w : E) :
    fderiv ℝ (fun y => leviTwoForm f y v w) z u +
      fderiv ℝ (fun y => leviTwoForm f y w u) z v +
      fderiv ℝ (fun y => leviTwoForm f y u v) z w = 0 := by
  rw [fderiv_leviTwoForm hf, fderiv_leviTwoForm hf, fderiv_leviTwoForm hf]
  have hA := (thirdFDeriv_swap_first hf u w (Complex.I • v)).trans
    (thirdFDeriv_swap_last hf w u (Complex.I • v))
  have hB := (thirdFDeriv_swap_last hf u (Complex.I • w) v).trans
    (thirdFDeriv_swap_first hf u v (Complex.I • w))
  have hC := (thirdFDeriv_swap_last hf v (Complex.I • u) w).trans
    (thirdFDeriv_swap_first hf v w (Complex.I • u))
  rw [hA, hB, hC]
  ring

end Yau.Blueprint.V03Proof
