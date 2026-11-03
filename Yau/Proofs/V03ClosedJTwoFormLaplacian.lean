import Yau.Proofs.V03JTwoFormAlgebra
import Yau.Proofs.V03LaplacianExchange

/-! A genuine smooth closed complex-invariant real two-form exchanges
the two complex directional Laplacians of its diagonal coefficients. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem closedJTwoForm_laplacian_exchange {U : Set E} (hU : IsOpen U)
    {Ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} (hΩ : ContDiffOn ℝ ∞ Ω U)
    (hclosed : ∀ q ∈ U, extDeriv Ω q = 0)
    (hJ : ∀ q ∈ U, ∀ u v : E, Ω q ![Complex.I • u, Complex.I • v] = Ω q ![u, v])
    (u v : E) {p : E} (hp : p ∈ U) :
    fderiv ℝ (fderiv ℝ (fun q => Ω q ![v, Complex.I • v])) p u u +
      fderiv ℝ (fderiv ℝ (fun q => Ω q ![v, Complex.I • v])) p (Complex.I • u) (Complex.I • u) =
    fderiv ℝ (fderiv ℝ (fun q => Ω q ![u, Complex.I • u])) p v v +
      fderiv ℝ (fderiv ℝ (fun q => Ω q ![u, Complex.I • u])) p (Complex.I • v) (Complex.I • v) := by
  let A : E → ℝ := fun q => Ω q ![v, Complex.I • v]
  let B : E → ℝ := fun q => Ω q ![u, Complex.I • u]
  let C : E → ℝ := fun q => Ω q ![u, v]
  let D : E → ℝ := fun q => Ω q ![u, Complex.I • v]
  have hA : ContDiffOn ℝ ∞ A U := twoFormCoefficient_contDiffOn hΩ v (Complex.I • v)
  have hB : ContDiffOn ℝ ∞ B U := twoFormCoefficient_contDiffOn hΩ u (Complex.I • u)
  have hC : ContDiffOn ℝ ∞ C U := twoFormCoefficient_contDiffOn hΩ u v
  have hD : ContDiffOn ℝ ∞ D U := twoFormCoefficient_contDiffOn hΩ u (Complex.I • v)
  have hdiff (q : E) (hq : q ∈ U) : DifferentiableAt ℝ Ω q :=
    (hΩ.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
  have hCd (q : E) (hq : q ∈ U) : DifferentiableAt ℝ C q :=
    (hC.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
  have hDd (q : E) (hq : q ∈ U) : DifferentiableAt ℝ D q :=
    (hD.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
  have h₁ (q : E) (hq : q ∈ U) : fderiv ℝ A q u = fderiv ℝ D q v - fderiv ℝ C q (Complex.I • v) := by
    have hh := congrArg (fun T : E [⋀^Fin 3]→L[ℝ] ℝ => T ![u, v, Complex.I • v]) (hclosed q hq)
    rw [extDeriv_twoForm_apply (hdiff q hq)] at hh
    simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply] at hh
    change fderiv ℝ A q u - fderiv ℝ D q v + fderiv ℝ C q (Complex.I • v) = 0 at hh
    linarith
  have h₂ (q : E) (hq : q ∈ U) : fderiv ℝ A q (Complex.I • u) =
      fderiv ℝ C q v + fderiv ℝ D q (Complex.I • v) := by
    have hJJ : (fun r => Ω r ![Complex.I • u, Complex.I • v]) =ᶠ[𝓝 q] C := by
      filter_upwards [hU.mem_nhds hq] with r hr
      exact hJ r hr u v
    have hcross : (fun r => Ω r ![Complex.I • u, v]) =ᶠ[𝓝 q] (fun r => -D r) := by
      filter_upwards [hU.mem_nhds hq] with r hr
      exact twoForm_Jcross (Ω r) (hJ r hr) u v
    have hh := congrArg (fun T : E [⋀^Fin 3]→L[ℝ] ℝ => T ![Complex.I • u, v, Complex.I • v])
      (hclosed q hq)
    rw [extDeriv_twoForm_apply (hdiff q hq), hJJ.fderiv_eq, hcross.fderiv_eq,
      fderiv_fun_neg (𝕜 := ℝ) (f := D) (x := q)] at hh
    simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply, ContinuousLinearMap.neg_apply] at hh
    change fderiv ℝ A q (Complex.I • u) - fderiv ℝ C q v +
      -fderiv ℝ D q (Complex.I • v) = 0 at hh
    linarith
  have h₃ (q : E) (hq : q ∈ U) : fderiv ℝ B q v =
      fderiv ℝ D q u + fderiv ℝ C q (Complex.I • u) := by
    have hcross : (fun r => Ω r ![v, Complex.I • u]) =ᶠ[𝓝 q] D := by
      filter_upwards [hU.mem_nhds hq] with r hr
      rw [twoForm_swap, twoForm_Jcross (Ω r) (hJ r hr) u v, neg_neg]
    have hswap : (fun r => Ω r ![v, u]) = (fun r => -C r) := by
      funext r
      exact twoForm_swap (Ω r) v u
    have hh := congrArg (fun T : E [⋀^Fin 3]→L[ℝ] ℝ => T ![v, u, Complex.I • u]) (hclosed q hq)
    rw [extDeriv_twoForm_apply (hdiff q hq), hcross.fderiv_eq, hswap,
      fderiv_fun_neg (𝕜 := ℝ) (f := C) (x := q)] at hh
    simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply, ContinuousLinearMap.neg_apply] at hh
    change fderiv ℝ B q v - fderiv ℝ D q u + -fderiv ℝ C q (Complex.I • u) = 0 at hh
    linarith
  have h₄ (q : E) (hq : q ∈ U) : fderiv ℝ B q (Complex.I • v) =
      fderiv ℝ D q (Complex.I • u) - fderiv ℝ C q u := by
    have hJJ : (fun r => Ω r ![Complex.I • v, Complex.I • u]) =ᶠ[𝓝 q] (fun r => -C r) := by
      filter_upwards [hU.mem_nhds hq] with r hr
      rw [hJ r hr v u]
      exact twoForm_swap (Ω r) v u
    have hswap : (fun r => Ω r ![Complex.I • v, u]) = (fun r => -D r) := by
      funext r
      exact twoForm_swap (Ω r) (Complex.I • v) u
    have hh := congrArg (fun T : E [⋀^Fin 3]→L[ℝ] ℝ => T ![Complex.I • v, u, Complex.I • u])
      (hclosed q hq)
    rw [extDeriv_twoForm_apply (hdiff q hq), hJJ.fderiv_eq, hswap,
      fderiv_fun_neg (𝕜 := ℝ) (f := C) (x := q), fderiv_fun_neg (𝕜 := ℝ) (f := D) (x := q)] at hh
    simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply, ContinuousLinearMap.neg_apply] at hh
    change fderiv ℝ B q (Complex.I • v) - -fderiv ℝ C q u + -fderiv ℝ D q (Complex.I • u) = 0 at hh
    linarith
  exact laplacian_exchange_of_closed_coefficients hU hA hB hC hD u (Complex.I • u) v (Complex.I • v)
    h₁ h₂ h₃ h₄ hp

end Yau.Blueprint.V03Proof
