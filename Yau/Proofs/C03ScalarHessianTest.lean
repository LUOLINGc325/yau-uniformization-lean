import Yau.Proofs.C03SecondOrderTaylor

/-! A negative scalar Hessian gives a whole complex-parameter neighborhood
of strict energy decrease. This uses the actual second derivative. -/

noncomputable section
open Filter Asymptotics
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem scalar_hessian_taylor (f : E → ℝ) (c : ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (hfirst : fderiv ℝ f 0 = 0)
    (hsecond : fderiv ℝ (fderiv ℝ f) 0 = (2 * c) • innerSL ℝ) :
    (fun x => f x - f 0 - c * ‖x‖ ^ 2) =o[𝓝 0] (fun x => ‖x‖ ^ 2) := by
  let q : E → ℝ := fun x => c * ‖x‖ ^ 2
  have hq : ContDiff ℝ 2 q := contDiff_const.mul (contDiff_norm_sq ℝ)
  have hqder : fderiv ℝ q = fun x => ((2 * c) • innerSL ℝ) x := by
    funext x
    dsimp only [q]
    rw [fderiv_const_mul ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.differentiableAt), fderiv_norm_sq_apply]
    ext y
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hq0 : fderiv ℝ q 0 = 0 := by rw [hqder]; simp
  have hq2 : fderiv ℝ (fderiv ℝ q) 0 = (2 * c) • innerSL ℝ := by
    rw [hqder]
    exact (((2 * c) • innerSL ℝ).hasFDerivAt).fderiv
  have hqD : DifferentiableAt ℝ (fderiv ℝ q) 0 := by
    rw [hqder]
    exact ((2 * c) • innerSL ℝ).differentiableAt
  have hfD : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
    (hf.fderiv_right (by norm_num)).differentiableAt_one
  have heq : fderiv ℝ (fun x => f x - q x) =ᶠ[𝓝 0]
      (fun x => fderiv ℝ f x - fderiv ℝ q x) := by
    filter_upwards [(hf.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).eventually (by norm_num)]
      with x hx
    exact fderiv_fun_sub hx.differentiableAt_one (hq.differentiable (by norm_num) x)
  have h1 : fderiv ℝ (fun x => f x - q x) 0 = 0 := by
    rw [fderiv_fun_sub (hf.differentiableAt (by norm_num))
      (hq.differentiable (by norm_num) 0), hfirst, hq0, sub_self]
  have h2 : fderiv ℝ (fderiv ℝ (fun x => f x - q x)) 0 = 0 := by
    rw [heq.fderiv_eq, fderiv_fun_sub hfD hqD, hsecond, hq2, sub_self]
  have H := second_order_littleO_of_zero_jets (fun x => f x - q x)
    (hf.sub hq.contDiffAt) h1 h2
  convert H using 1
  funext x
  dsimp only [q]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero]
  ring

theorem eventually_lt_of_scalar_negative_hessian (f : E → ℝ) (c : ℝ) (hc : c < 0)
    (hf : ContDiffAt ℝ 2 f 0) (hfirst : fderiv ℝ f 0 = 0)
    (hsecond : fderiv ℝ (fderiv ℝ f) 0 = (2 * c) • innerSL ℝ) :
    ∀ᶠ x in 𝓝 (0 : E), x ≠ 0 → f x < f 0 :=
  eventually_lt_of_negative_quadratic f c hc (scalar_hessian_taylor f c hf hfirst hsecond)

end Yau.Proofs.C03Aux
