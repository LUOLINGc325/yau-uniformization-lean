import Yau.Proofs.F01RayleighPenalty
import Yau.Proofs.F01ConformalGradient
import Yau.Proofs.F01MixedWirtingerLinearity

/-! The gradient relation is derived from an actual spatial maximum of
the actual penalized scalar, rather than supplied as a contact oracle. -/
noncomputable section
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem penalty_contact_wirtinger_jet (u Q f : ComplexVector n → ℝ)
    {z : ComplexVector n} (hu : DifferentiableAt ℝ u z)
    (hQ : DifferentiableAt ℝ Q z) (hf : DifferentiableAt ℝ f z)
    (a δ : ℝ) (hden : 1 + a * Q z ≠ 0)
    (hmax : IsLocalMax (fun w => u w - rayleighPenalty a (Q w) - δ * f w) z)
    (v : ComplexVector n) :
    wirt (fun w => (u w : ℂ)) z v =
      ((deriv (rayleighPenalty a) (Q z) : ℝ) : ℂ) * wirt (fun w => (Q w : ℂ)) z v +
        (δ : ℂ) * wirt (fun w => (f w : ℂ)) z v := by
  have hJ : HasDerivAt (rayleighPenalty a) (deriv (rayleighPenalty a) (Q z)) (Q z) :=
    (rayleighPenalty_hasDerivAt a (Q z) hden).differentiableAt.hasDerivAt
  have hδ : HasDerivAt (fun s : ℝ => δ * s) δ (f z) := by
    convert (hasDerivAt_id (f z)).const_mul δ using 1 <;> simp
  have hJQ : DifferentiableAt ℝ (fun w => rayleighPenalty a (Q w)) z :=
    hJ.differentiableAt.comp z hQ
  have hδf : DifferentiableAt ℝ (fun w => δ * f w) z := (differentiableAt_const δ).mul hf
  have htest : DifferentiableAt ℝ (fun w => u w - rayleighPenalty a (Q w) - δ * f w) z :=
    (hu.sub hJQ).sub hδf
  have hzero : wirt (fun w => ((u w - rayleighPenalty a (Q w) - δ * f w : ℝ) : ℂ)) z v = 0 := by
    have hd : fderiv ℝ (fun w => ((u w - rayleighPenalty a (Q w) - δ * f w : ℝ) : ℂ)) z =
        Complex.ofRealCLM.comp (fderiv ℝ (fun w => u w - rayleighPenalty a (Q w) - δ * f w) z) := by
      change fderiv ℝ (Complex.ofRealCLM ∘ (fun w => u w - rayleighPenalty a (Q w) - δ * f w)) z = _
      rw [fderiv_comp z Complex.ofRealCLM.differentiableAt htest, ContinuousLinearMap.fderiv]
    simp only [wirt, hd, hmax.fderiv_eq_zero, ContinuousLinearMap.comp_zero,
      zero_apply, mul_zero, sub_self]
  have huc : DifferentiableAt ℝ (fun w => (u w : ℂ)) z := Complex.ofRealCLM.differentiableAt.comp z hu
  have hJc : DifferentiableAt ℝ (fun w => (rayleighPenalty a (Q w) : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hJQ
  have hδc : DifferentiableAt ℝ (fun w => ((δ * f w : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hδf
  have heq : (fun w => ((u w - rayleighPenalty a (Q w) - δ * f w : ℝ) : ℂ)) =
      (fun w => (u w : ℂ) - (rayleighPenalty a (Q w) : ℂ) - ((δ * f w : ℝ) : ℂ)) := by
    funext w
    push_cast
    rfl
  rw [heq, wirt_sub_rule
      (fun w : ComplexVector n => (u w : ℂ) - (rayleighPenalty a (Q w) : ℂ))
      (fun w : ComplexVector n => ((δ * f w : ℝ) : ℂ)) z v (huc.sub hJc) hδc,
    wirt_sub_rule (fun w : ComplexVector n => (u w : ℂ))
      (fun w : ComplexVector n => (rayleighPenalty a (Q w) : ℂ)) z v huc hJc,
    wirt_ofReal_scalar_comp hQ hJ v, wirt_ofReal_scalar_comp hf hδ v] at hzero
  linear_combination hzero

end Yau.NodeProofs.F01Aux
