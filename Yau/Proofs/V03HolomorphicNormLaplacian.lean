import Yau.Proofs.V03ClosedLaplacian
import Yau.Proofs.V03HolomorphicQuadratic
import Yau.Proofs.V03EuclideanRadial

/-! The genuine squared norm of a holomorphic closed disc has Laplacian
four times its actual derivative density, and its boundary gradient has
the exact Hermitian first-derivative expression. -/

open scoped Topology ContDiff RealInnerProductSpace

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem closedLaplacian_holomorphic_norm_sq {f : ℂ → H} {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) (hf : ContDiffAt ℂ 2 f z) :
    closedLaplacian (fun w => ‖f w‖ ^ 2) z = 4 * ‖fderiv ℂ f z 1‖ ^ 2 := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  have hreal (v : ℂ) : fderiv ℝ f z v = fderiv ℂ f z v :=
    congrArg (fun A : ℂ →L[ℝ] H => A v) ((hf.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ)
  have hII : fderiv ℝ (fderiv ℝ f) z Complex.I Complex.I =
      -fderiv ℝ (fderiv ℝ f) z 1 1 := by
    simpa only [smul_eq_mul, mul_one] using secondFDeriv_complex_I_I hf (1 : ℂ) (1 : ℂ)
  have hI : fderiv ℂ f z Complex.I = Complex.I • fderiv ℂ f z 1 := by
    simpa only [smul_eq_mul, mul_one] using (fderiv ℂ f z).map_smul Complex.I (1 : ℂ)
  rw [closedLaplacian_eq hz, secondFDeriv_norm_sq_comp (hf.restrict_scalars ℝ),
    secondFDeriv_norm_sq_comp (hf.restrict_scalars ℝ), hII]
  simp only [inner_neg_right, real_inner_self_eq_norm_sq, hreal, hI,
    norm_smul, Complex.norm_I, one_mul]
  ring

theorem closedRealGradient_holomorphic_norm_sq {f : ℂ → H}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) (v : ℂ) :
    closedRealGradient (fun w => ‖f w‖ ^ 2) z v =
      2 * (inner ℂ (f z) (fderivWithin ℂ f (Metric.closedBall 0 1) z v)).re := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  have hd := (((hf.differentiableOn (by simp)) z hz).hasFDerivWithinAt.restrictScalars ℝ).norm_sq
  have he := congrArg (fun A : ℂ →L[ℝ] ℝ => A v)
    (hd.fderivWithin (uniqueDiffOn_real_closedDisc z hz))
  simpa only [closedRealGradient, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply, real_inner_eq_re_inner,
    two_smul, two_mul, add_apply, RCLike.re_eq_complex_re] using he

end Yau.Blueprint.V03Proof
