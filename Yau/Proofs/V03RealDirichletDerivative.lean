import Yau.Proofs.V03RealAngularTrace
import Yau.Proofs.V03FourierTraceOperator

/-! The actual real derivative of the native half-order Hilbert trace
equals the Hilbert trace of the actual parameter derivative. -/

open scoped Topology ContDiff lp
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem realAngularDirichletVector_coeff {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    {z : ℂ} (hz : z ∈ U) (hp : Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi)) (k : ℤ) :
    angularDirichletVector hU hf z k =
      (Real.sqrt |(k : ℝ)| : ℂ) * intervalFourierCoeffL k (realFamilyUniformTrace hf z) := by
  rw [angularDirichletVector_coeff hU hf hz hp,
    intervalFourierCoeffL_apply k hp _ (fun θ => realFamilyUniformTrace_apply hf hz θ)]
  rfl

theorem fderiv_realAngularDirichletVector_coeff {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (hp : ∀ z ∈ U, Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi))
    {z : ℂ} (hz : z ∈ U) (v : ℂ) (k : ℤ) :
    fderiv ℝ (angularDirichletVector hU hf) z v k =
      dirichletCoeff (fun θ => realParameterDerivative f v (z, θ)) k := by
  have hQ : DifferentiableAt ℝ (angularDirichletVector hU hf) z :=
    ((angularDirichletVector_contDiffOn hU hf).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hT : DifferentiableAt ℝ (realFamilyUniformTrace hf) z :=
    ((realFamilyUniformTrace_contDiffOn hU hf).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  rw [fderiv_real_l2_eval hQ v k]
  have heq : (fun p => angularDirichletVector hU hf p k) =ᶠ[𝓝 z]
      (fun p => (Real.sqrt |(k : ℝ)| : ℂ) * intervalFourierCoeffL k (realFamilyUniformTrace hf p)) := by
    filter_upwards [hU.mem_nhds hz] with p hpU
    exact realAngularDirichletVector_coeff hU hf hpU (hp p hpU) k
  rw [heq.fderiv_eq]
  have hh := (((intervalFourierCoeffL k).restrictScalars ℝ).hasFDerivAt.comp z
    hT.hasFDerivAt).const_mul (Real.sqrt |(k : ℝ)| : ℂ)
  have he := congrArg (fun A : ℂ →L[ℝ] ℂ => A v) hh.fderiv
  calc
    _ = (Real.sqrt |(k : ℝ)| : ℂ) * intervalFourierCoeffL k
        (fderiv ℝ (realFamilyUniformTrace hf) z v) := by
      simpa only [Function.comp_def, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars', smul_eq_mul] using he
    _ = _ := by
      rw [intervalFourierCoeffL_apply k (realParameterDerivative_periodic hU hf hp hz v) _
        (fun θ => fderiv_realFamilyUniformTrace_apply hU hf hz v θ)]
      rfl

theorem fderiv_realAngularDirichletVector {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (hp : ∀ z ∈ U, Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi))
    {z : ℂ} (hz : z ∈ U) (v : ℂ) :
    fderiv ℝ (angularDirichletVector hU hf) z v =
      angularDirichletVector hU (realParameterDerivative_contDiffOn hU hf v) z := by
  apply Subtype.ext
  funext k
  exact (fderiv_realAngularDirichletVector_coeff hU hf hp hz v k).trans
    (angularDirichletVector_coeff hU (realParameterDerivative_contDiffOn hU hf v) hz
      (realParameterDerivative_periodic hU hf hp hz v) k).symm

theorem fderiv_realAngularDirichletVector_norm_sq {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (hp : ∀ z ∈ U, Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi))
    {z : ℂ} (hz : z ∈ U) (v : ℂ) :
    ‖fderiv ℝ (angularDirichletVector hU hf) z v‖ ^ 2 =
      (boundaryDSq (fun θ (_ : Unit) => realParameterDerivative f v (z, θ))).toReal := by
  rw [fderiv_realAngularDirichletVector hU hf hp hz v]
  exact angularDirichletVector_norm_sq hU (realParameterDerivative_contDiffOn hU hf v) hz
    (realParameterDerivative_periodic hU hf hp hz v)

theorem secondFDeriv_realAngularDirichletVector {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (hp : ∀ z ∈ U, Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi))
    {z : ℂ} (hz : z ∈ U) (v w : ℂ) :
    fderiv ℝ (fderiv ℝ (angularDirichletVector hU hf)) z w v =
      angularDirichletVector hU
        (realParameterDerivative_contDiffOn hU (realParameterDerivative_contDiffOn hU hf v) w) z := by
  have hQ : ContDiffAt ℝ ∞ (angularDirichletVector hU hf) z :=
    (angularDirichletVector_contDiffOn hU hf).contDiffAt (hU.mem_nhds hz)
  rw [fderiv_real_clm_apply ((hQ.fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero) w v]
  have heq : (fun p => fderiv ℝ (angularDirichletVector hU hf) p v) =ᶠ[𝓝 z]
      angularDirichletVector hU (realParameterDerivative_contDiffOn hU hf v) := by
    filter_upwards [hU.mem_nhds hz] with p hpU
    exact fderiv_realAngularDirichletVector hU hf hp hpU v
  rw [heq.fderiv_eq]
  exact fderiv_realAngularDirichletVector hU (realParameterDerivative_contDiffOn hU hf v)
    (fun p hpU => realParameterDerivative_periodic hU hf hp hpU v) hz w

end Yau.Blueprint.V03Proof
