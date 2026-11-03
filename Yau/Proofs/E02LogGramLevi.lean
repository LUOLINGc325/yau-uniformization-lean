import Yau.Proofs.E02LogGramSecond
import Yau.Proofs.E02LogGramLeviAlgebra

open Matrix Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The actual rectangular Levi is the nonnegative tangent-square
trace, from the computed first derivative of the genuine log-Gram map.
The literal logdet discharges these ordinary calculus inputs separately. -/
theorem rectLevi_eq_tangent_of_gram_logderivative {n m : ℕ} (f : Rect n m → ℝ)
    (M Z : Rect n m) (hM : (M*Mᴴ).PosDef) (hf : ContDiffAt ℝ 2 f M)
    (hInv : DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M)
    (hFirst : ∀ᶠ N in 𝓝 M, ∀ V : Rect n m,
      fderiv ℝ f N V = (Matrix.trace ((N*Nᴴ)⁻¹*(N*Vᴴ+V*Nᴴ))).re) :
    rectLevi f M Z = (Matrix.trace (projectorTangent M Z*(projectorTangent M Z)ᴴ)).re := by
  unfold rectLevi
  rw [second_fderiv_of_gram_logderivative f M Z Z hM hf hInv hFirst,
    second_fderiv_of_gram_logderivative f M (Complex.I • Z) (Complex.I • Z) hM hf hInv hFirst]
  exact gram_log_hessian_trace_eq_tangent M Z hM

theorem rectLevi_nonneg_of_gram_logderivative {n m : ℕ} (f : Rect n m → ℝ)
    (M Z : Rect n m) (hM : (M*Mᴴ).PosDef) (hf : ContDiffAt ℝ 2 f M)
    (hInv : DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M)
    (hFirst : ∀ᶠ N in 𝓝 M, ∀ V : Rect n m,
      fderiv ℝ f N V = (Matrix.trace ((N*Nᴴ)⁻¹*(N*Vᴴ+V*Nᴴ))).re) :
    0 ≤ rectLevi f M Z := by
  rw [rectLevi_eq_tangent_of_gram_logderivative f M Z hM hf hInv hFirst]
  exact (RCLike.nonneg_iff.mp (Matrix.posSemidef_self_mul_conjTranspose
    (projectorTangent M Z)).trace_nonneg).1

end Yau.NodeProofs.E02Aux
