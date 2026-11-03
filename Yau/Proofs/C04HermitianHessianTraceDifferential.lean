import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

/-! Differentiate the actual complex intertwining equation. No metric or
connection is independent output data: the Hessian is the displayed formula. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def scalarCovariantHessian (u : E → ℂ) (x : E) (G : E →L[ℝ] E →L[ℝ] E)
    (v w : E) : ℂ :=
  fderiv ℝ (fderiv ℝ u) x v w - fderiv ℝ u x (G v w)

theorem scalar_complex_intertwining_derivative
    (u : E → ℂ) (J : E → E →L[ℝ] E) (x : E)
    (hu : ContDiffAt ℝ 2 u x) (hJ : DifferentiableAt ℝ J x)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ v, fderiv ℝ u y (J y v) = Complex.I * fderiv ℝ u y v)
    (v w : E) :
    fderiv ℝ u x (fderiv ℝ J x v w) +
      fderiv ℝ (fderiv ℝ u) x v (J x w) =
        Complex.I * fderiv ℝ (fderiv ℝ u) x v w := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hJw : HasFDerivAt (fun y => J y w) ((fderiv ℝ J x).flip w) x := by
    simpa using hJ.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hduw : HasFDerivAt (fun y => fderiv ℝ u y w)
      ((fderiv ℝ (fderiv ℝ u) x).flip w) x := by
    simpa using hdu.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hl := hdu.hasFDerivAt.clm_apply hJw
  have hr := hduw.const_mul Complex.I
  have he : (fun y => fderiv ℝ u y (J y w)) =ᶠ[𝓝 x]
      (fun y => Complex.I * fderiv ℝ u y w) := hrel.mono fun y hy => hy w
  have heq : fderiv ℝ (fun y => fderiv ℝ u y (J y w)) x =
      fderiv ℝ (fun y => Complex.I * fderiv ℝ u y w) x := he.fderiv_eq
  rw [hl.fderiv, hr.fderiv] at heq
  exact congrArg (fun L : E →L[ℝ] ℂ => L v) heq

theorem scalar_covariant_hessian_complex_right
    (u : E → ℂ) (J : E → E →L[ℝ] E) (x : E)
    (hu : ContDiffAt ℝ 2 u x) (hJ : DifferentiableAt ℝ J x)
    (G : E →L[ℝ] E →L[ℝ] E)
    (hpar : ∀ v w, fderiv ℝ J x v w + G v (J x w) = J x (G v w))
    (hrel : ∀ᶠ y in 𝓝 x, ∀ v, fderiv ℝ u y (J y v) = Complex.I * fderiv ℝ u y v)
    (v w : E) :
    scalarCovariantHessian u x G v (J x w) =
      Complex.I * scalarCovariantHessian u x G v w := by
  have hd := scalar_complex_intertwining_derivative u J x hu hJ hrel v w
  have hp := congrArg (fderiv ℝ u x) (hpar v w)
  rw [map_add, hrel.self_of_nhds] at hp
  dsimp [scalarCovariantHessian]
  rw [mul_sub]
  linear_combination hd - hp

theorem scalar_covariant_hessian_symm (u : E → ℂ) (x : E)
    (hu : ContDiffAt ℝ 2 u x) (G : E →L[ℝ] E →L[ℝ] E)
    (hG : ∀ v w, G v w = G w v) (v w : E) :
    scalarCovariantHessian u x G v w = scalarCovariantHessian u x G w v := by
  dsimp [scalarCovariantHessian]
  rw [hu.isSymmSndFDerivAt (by norm_num) v w, hG v w]

end Yau.Proofs.C04Aux
