import Yau.Proofs.F01ScalarHeatChain
import Yau.Proofs.F01ScalarLeviLinearity
import Yau.Proofs.F01RayleighPenalty

/-! Exact closed-time heat decomposition of the actual penalized test
function, with its concave scalar Hessian and the properness penalty. -/
noncomputable section
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem traceWith_real_smul (H A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) :
    traceWith H ((c : ℂ) • A) = c * traceWith H A := by
  simp only [traceWith, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem rayleighPenalty_contDiffAt (a v : ℝ) (hden : 1 + a * v ≠ 0) :
    ContDiffAt ℝ ∞ (rayleighPenalty a) v := by
  have hlinear : ContDiffAt ℝ ∞ (fun s : ℝ => a * s) v := contDiffAt_const.mul contDiffAt_id
  have hlog : ContDiffAt ℝ ∞ (fun s : ℝ => Real.log (1 + a * s)) v :=
    (contDiffAt_const.add hlinear).log hden
  exact hlinear.add hlog

theorem penalized_heat_chain_within (values : Fin n → ℝ) (hv : ∀ i, values i ≠ 0)
    (U Q : ComplexVector n × ℝ → ℝ) (f : ComplexVector n → ℝ) (F : ℝ → ℝ)
    {z : ComplexVector n} {t δ : ℝ} {I : Set ℝ}
    (hUnique : UniqueDiffWithinAt ℝ I t)
    (hUtime : DifferentiableWithinAt ℝ (fun s => U (z, s)) I t)
    (hQtime : DifferentiableWithinAt ℝ (fun s => Q (z, s)) I t)
    (hUspace : ContDiffAt ℝ 2 (fun w => U (w, t)) z)
    (hQspace : ContDiffAt ℝ 2 (fun w => Q (w, t)) z)
    (hf : ContDiffAt ℝ 2 f z) (hF : ContDiffAt ℝ 2 F (Q (z, t))) :
    derivWithin (fun s => U (z, s) - F (Q (z, s)) - δ * f z) I t -
      traceWith (Matrix.diagonal (fun i => (values i : ℂ)))
        (leviC (fun w => U (w, t) - F (Q (w, t)) - δ * f w) z) =
      (derivWithin (fun s => U (z, s)) I t -
        traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (leviC (fun w => U (w, t)) z)) -
      deriv F (Q (z, t)) * (derivWithin (fun s => Q (z, s)) I t -
        traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (leviC (fun w => Q (w, t)) z)) +
      deriv (deriv F) (Q (z, t)) *
        dualNormMat (Matrix.diagonal (fun i => (values i : ℂ))) (WithLp.toLp 2
          (fun i => wirt (fun w => (Q (w, t) : ℂ)) z (stdVec i))) +
      δ * traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (leviC f z) := by
  have hFtime := (hF.differentiableAt (by norm_num)).hasDerivAt.comp_hasDerivWithinAt t
    hQtime.hasDerivWithinAt
  have ht := ((hUtime.hasDerivWithinAt.sub hFtime).sub
    (hasDerivWithinAt_const t I (δ * f z))).derivWithin hUnique
  change derivWithin (fun s => U (z, s) - F (Q (z, s)) - δ * f z) I t =
    derivWithin (fun s => U (z, s)) I t -
      deriv F (Q (z, t)) * derivWithin (fun s => Q (z, s)) I t - 0 at ht
  have hcomp : ContDiffAt ℝ 2 (fun w => F (Q (w, t))) z := hF.comp z hQspace
  have hδf : ContDiffAt ℝ 2 (fun w => δ * f w) z := contDiffAt_const.mul hf
  rw [ht, leviC_sub (f := fun w => U (w, t) - F (Q (w, t))) (g := fun w => δ * f w)
      (hUspace.sub hcomp) hδf,
    leviC_sub (f := fun w => U (w, t)) (g := fun w => F (Q (w, t))) hUspace hcomp,
    leviC_const_mul hf δ, traceWith_sub, traceWith_sub, traceWith_real_smul,
    traceWith_scalar_levi_real_diagonal values hv hQspace hF]
  ring

end Yau.NodeProofs.F01Aux
