import Yau.Proofs.V03HolomorphicUniformTrace
import Yau.Proofs.V03FourierTraceOperator

/-! The derivative of the actual family Dirichlet vector is exactly the
weighted Fourier vector of the actual parameter velocity. -/

open scoped Topology ContDiff lp
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

def jointParameterVelocity (H : ℂ × ℂ → ℂ) (U : Set ℂ) (z v ζ : ℂ) : ℂ :=
  fderivWithin ℂ H (U ×ˢ Metric.closedBall (0 : ℂ) 1) (z, ζ) (v, 0)

theorem holomorphicFamilyDirichletVector_coeff {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ U) (k : ℤ) :
    holomorphicFamilyDirichletVector hU hH z k =
      (Real.sqrt |(k : ℝ)| : ℂ) * intervalFourierCoeffL k (holomorphicFamilyUniformTrace hH z) := by
  calc
    _ = dirichletCoeff (fun θ => H (z, circlePoint θ)) k :=
      angularDirichletVector_coeff hU (holomorphicBoundaryFamily_contDiffOn hH) hz
        (circleTrace_periodic (fun ζ => H (z, ζ))) k
    _ = _ := by
      rw [intervalFourierCoeffL_apply k (circleTrace_periodic (fun ζ => H (z, ζ))) _
        (fun θ => holomorphicFamilyUniformTrace_apply hH hz θ)]
      rfl

theorem fderiv_holomorphicFamilyDirichletVector_coeff {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ U) (v : ℂ) (k : ℤ) :
    fderiv ℂ (holomorphicFamilyDirichletVector hU hH) z v k =
      dirichletCoeff (fun θ => jointParameterVelocity H U z v (circlePoint θ)) k := by
  have hQ : DifferentiableAt ℂ (holomorphicFamilyDirichletVector hU hH) z :=
    ((holomorphicFamilyDirichletVector_contDiffOn hU hH).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hT : DifferentiableAt ℂ (holomorphicFamilyUniformTrace hH) z :=
    ((holomorphicFamilyUniformTrace_contDiffOn hU hH).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  rw [fderiv_l2_eval hQ v k]
  have heq : (fun p => holomorphicFamilyDirichletVector hU hH p k) =ᶠ[𝓝 z]
      (fun p => (Real.sqrt |(k : ℝ)| : ℂ) *
        intervalFourierCoeffL k (holomorphicFamilyUniformTrace hH p)) := by
    filter_upwards [hU.mem_nhds hz] with p hp
    exact holomorphicFamilyDirichletVector_coeff hU hH hp k
  rw [heq.fderiv_eq]
  have hh := ((intervalFourierCoeffL k).hasFDerivAt.comp z hT.hasFDerivAt).const_mul
    (Real.sqrt |(k : ℝ)| : ℂ)
  have he := congrArg (fun A : ℂ →L[ℂ] ℂ => A v) hh.fderiv
  calc
    _ = (Real.sqrt |(k : ℝ)| : ℂ) * intervalFourierCoeffL k
        (fderiv ℂ (holomorphicFamilyUniformTrace hH) z v) := by
      simpa only [Function.comp_def, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        smul_eq_mul] using he
    _ = _ := by
      rw [intervalFourierCoeffL_apply k
        (circleTrace_periodic (jointParameterVelocity H U z v)) _
        (fun θ => fderiv_holomorphicFamilyUniformTrace_apply hU hH hz v θ)]
      rfl

theorem fderiv_holomorphicFamilyDirichletVector_norm_sq {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ U) (v : ℂ) :
    ‖fderiv ℂ (holomorphicFamilyDirichletVector hU hH) z v‖ ^ 2 =
      (boundaryDSq (fun θ (_ : Unit) => jointParameterVelocity H U z v (circlePoint θ))).toReal := by
  let V : ℝ → ℂ := fun θ => jointParameterVelocity H U z v (circlePoint θ)
  let W := fderiv ℂ (holomorphicFamilyDirichletVector hU hH) z v
  have heq : dirichletCoeff V = (W : ℤ → ℂ) := by
    funext k
    exact (fderiv_holomorphicFamilyDirichletVector_coeff hU hH hz v k).symm
  have hmem : Memℓp (dirichletCoeff V) 2 := by
    rw [heq]
    exact W.2
  have hfin := (dirichletCoeff_mem_iff V).mp hmem
  have hW : W = dirichletVector V hfin := by
    apply Subtype.ext
    exact heq.symm
  rw [show fderiv ℂ (holomorphicFamilyDirichletVector hU hH) z v = W from rfl, hW,
    dirichletVector_norm_sq]

end Yau.Blueprint.V03Proof
