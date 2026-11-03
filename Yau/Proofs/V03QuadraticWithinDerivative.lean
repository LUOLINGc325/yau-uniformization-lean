import Yau.Proofs.V03BoundaryDerivative
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! Genuine directional differentiation of Hermitian quadratic fields
within the original closed parameter set. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderivWithin_star_mul_mul_apply {S : Set E} {x : E}
    (hS : UniqueDiffWithinAt ℝ S x) {a b c : E → ℂ}
    (ha : DifferentiableWithinAt ℝ a S x) (hb : DifferentiableWithinAt ℝ b S x)
    (hc : DifferentiableWithinAt ℝ c S x) (v : E) :
    fderivWithin ℝ (fun y => star (a y) * b y * c y) S x v =
      star (fderivWithin ℝ a S x v) * b x * c x +
        star (a x) * fderivWithin ℝ b S x v * c x +
          star (a x) * b x * fderivWithin ℝ c S x v := by
  have hab : DifferentiableWithinAt ℝ (fun y => star (a y) * b y) S x := ha.star.mul hb
  rw [fderivWithin_fun_mul (c := fun y => star (a y) * b y) (d := c) hS hab hc,
    fderivWithin_fun_mul (c := fun y => star (a y)) (d := b) hS ha.star hb, fderivWithin_star hS]
  have hs (w : ℂ) : ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) w = star w := rfl
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    hs]
  ring

theorem fderivWithin_two_re_apply {S : Set E} {x : E}
    (hS : UniqueDiffWithinAt ℝ S x) {f : E → ℂ} (hf : DifferentiableWithinAt ℝ f S x) (v : E) :
    fderivWithin ℝ (fun y => 2 * (f y).re) S x v = 2 * (fderivWithin ℝ f S x v).re := by
  let A : ℂ →L[ℝ] ℝ := (2 : ℝ) • Complex.reCLM
  have hh := congrArg (fun T : E →L[ℝ] ℝ => T v)
    ((A.hasFDerivAt.comp_hasFDerivWithinAt x hf.hasFDerivWithinAt).fderivWithin hS)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, A, smul_apply,
    smul_eq_mul, Complex.reCLM_apply] using hh

end Yau.Blueprint.V03Proof
