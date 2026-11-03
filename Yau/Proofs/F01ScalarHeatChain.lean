import Yau.Proofs.F01LogLaplacianDiagonal

/-! The actual scalar heat chain rule in the diagonal metric frame,
including the original within-time derivative at closed time faces. -/
noncomputable section
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem traceWith_scalar_levi_real_diagonal (values : Fin n → ℝ)
    (hv : ∀ i, values i ≠ 0) {Q : ComplexVector n → ℝ} {F : ℝ → ℝ}
    {z : ComplexVector n} (hQ : ContDiffAt ℝ 2 Q z)
    (hF : ContDiffAt ℝ 2 F (Q z)) :
    traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (leviC (fun w => F (Q w)) z) =
      deriv F (Q z) * traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (leviC Q z) +
        deriv (deriv F) (Q z) * dualNormMat (Matrix.diagonal (fun i => (values i : ℂ)))
          (WithLp.toLp 2 (fun i => wirt (fun w => (Q w : ℂ)) z (stdVec i))) := by
  rw [traceWith_real_diagonal values hv, traceWith_real_diagonal values hv,
    dualNormMat_real_diagonal values hv, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [scalar_levi_diagonal_comp hQ hF]
  ring

theorem local_heat_scalar_comp_within (values : Fin n → ℝ) (hv : ∀ i, values i ≠ 0)
    {Q : ComplexVector n → ℝ} {F qcurve : ℝ → ℝ} {z : ComplexVector n} {t : ℝ}
    {I : Set ℝ} (hUnique : UniqueDiffWithinAt ℝ I t)
    (hcurve : DifferentiableWithinAt ℝ qcurve I t) (hqt : qcurve t = Q z)
    (hQ : ContDiffAt ℝ 2 Q z) (hF : ContDiffAt ℝ 2 F (Q z)) :
    derivWithin (fun s => F (qcurve s)) I t -
        traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (leviC (fun w => F (Q w)) z) =
      deriv F (Q z) * (derivWithin qcurve I t -
        traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (leviC Q z)) -
      deriv (deriv F) (Q z) * dualNormMat (Matrix.diagonal (fun i => (values i : ℂ)))
        (WithLp.toLp 2 (fun i => wirt (fun w => (Q w : ℂ)) z (stdVec i))) := by
  have hFd : HasDerivAt F (deriv F (Q z)) (qcurve t) := by
    rw [hqt]
    exact (hF.differentiableAt (by norm_num)).hasDerivAt
  have ht := (hFd.comp_hasDerivWithinAt t hcurve.hasDerivWithinAt).derivWithin hUnique
  change derivWithin (fun s => F (qcurve s)) I t =
    deriv F (Q z) * derivWithin qcurve I t at ht
  rw [ht, traceWith_scalar_levi_real_diagonal values hv hQ hF]
  ring

end Yau.NodeProofs.F01Aux
