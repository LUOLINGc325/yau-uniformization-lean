import Yau.Proofs.P08ExhaustionProfile

noncomputable section
open scoped Topology ContDiff
namespace Yau.NodeProofs.P08Aux

def exhaustionScaledProfile (a : ℝ) (s : ℝ) : ℝ := exhaustionProfile (s / a)

theorem exhaustionScaledProfile_contDiff (a : ℝ) :
    ContDiff ℝ ∞ (exhaustionScaledProfile a) :=
  exhaustionProfile.contDiff.comp (contDiff_id.div_const a)

theorem exhaustionScaledProfile_deriv (a s : ℝ) :
    deriv (exhaustionScaledProfile a) s = deriv (exhaustionProfile : ℝ → ℝ) (s / a) / a := by
  have hCD : ContDiff ℝ ∞ (exhaustionProfile : ℝ → ℝ) := exhaustionProfile.contDiff
  have h := ((hCD.differentiable (by simp) (s / a)).hasDerivAt).comp s
    ((hasDerivAt_id s).div_const a)
  change deriv (fun t => exhaustionProfile (t / a)) s = _
  simpa only [Function.comp_def, id_eq, one_div, one_mul, div_eq_mul_inv] using h.deriv

theorem exhaustionScaledProfile_deriv_deriv (a s : ℝ) :
    deriv (deriv (exhaustionScaledProfile a)) s =
      deriv (deriv (exhaustionProfile : ℝ → ℝ)) (s / a) / a ^ 2 := by
  have hd : ContDiff ℝ ∞ (deriv (exhaustionProfile : ℝ → ℝ)) :=
    (contDiff_infty_iff_deriv.mp exhaustionProfile.contDiff).2
  have heq : deriv (exhaustionScaledProfile a) = fun t =>
      deriv (exhaustionProfile : ℝ → ℝ) (t / a) / a :=
    funext (exhaustionScaledProfile_deriv a)
  have h := (((hd.differentiable (by simp) (s / a)).hasDerivAt).comp s
    ((hasDerivAt_id s).div_const a)).div_const a
  rw [heq]
  have hh : deriv (fun t => deriv (exhaustionProfile : ℝ → ℝ) (t / a) / a) s =
      (deriv (deriv (exhaustionProfile : ℝ → ℝ)) (s / a) * (1 / a)) / a := by
    simpa only [Function.comp_def, id_eq] using h.deriv
  rw [hh]
  ring


end Yau.NodeProofs.P08Aux
