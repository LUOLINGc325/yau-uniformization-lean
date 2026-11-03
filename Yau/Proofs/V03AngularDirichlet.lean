import Yau.Proofs.V03AngularTrace
import Yau.Proofs.V03IntervalPeriodicLp
import Yau.Proofs.V03FourierDecay

/-! The original periodic half-order energy is the exact norm square of a
genuinely smooth Hilbert-valued parameter map built from the angular trace.
No infinite-series differentiation or finiteness oracle is assumed. -/

open scoped Topology ContDiff lp
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

def intervalDirichletL : C(BoundaryAngleInterval, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) :=
  dirichletFromAngular.comp intervalCircleLpL

def angularDirichletVector {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) (z : ℂ) : ℓ²(ℤ, ℂ) :=
  intervalDirichletL (angularCompactTrace hU hf z)

theorem angularDirichletVector_contDiffOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (angularDirichletVector hU hf) U := by
  change ContDiffOn ℝ ∞ (fun z =>
    (intervalDirichletL.restrictScalars ℝ) (angularCompactTrace hU hf z)) U
  have hh := (intervalDirichletL.restrictScalars ℝ).contDiff.comp_contDiffOn
    (angularCompactTrace_contDiffOn hU hf)
  simpa only [Function.comp_def] using hh

theorem parameter_angle_slice_contDiff {U : Set ℂ} {f : ℂ × ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) {z : ℂ} (hz : z ∈ U) :
    ContDiff ℝ ∞ (fun θ => f (z, θ)) := by
  apply contDiffOn_univ.mp
  exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun θ (_ : θ ∈ (Set.univ : Set ℝ)) => ⟨hz, Set.mem_univ θ⟩)

theorem angularDirichletVector_coeff {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) {z : ℂ} (hz : z ∈ U)
    (hp : Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi)) (k : ℤ) :
    angularDirichletVector hU hf z k = dirichletCoeff (fun θ => f (z, θ)) k := by
  have hu := parameter_angle_slice_contDiff hf hz
  have hmatch (θ : BoundaryAngleInterval) :
      angularCompactTrace hU hf z θ = deriv (fun t => f (z, t)) θ :=
    angularCompactTrace_apply hU hf hz θ
  change dirichletFromAngular (intervalCircleLpL (angularCompactTrace hU hf z)) k = _
  rw [dirichletFromAngular_apply, intervalCircleLpL_apply,
    intervalTraceLp_fourierCoeff (periodic_deriv hp) _ hmatch]
  by_cases hk : k = 0
  · subst k
    simp [inverseAngularMultiplier, dirichletCoeff]
  · have hc := circleFourier_of_hasDerivAt (u := fun θ => f (z, θ)) hk
      (fun θ _ => (hu.differentiable (by simp) θ).hasDerivAt)
      ((hu.continuous_deriv (by simp)).intervalIntegrable _ _)
      (by simpa only [zero_add] using hp 0)
    rw [dirichletCoeff, hc, inverseAngularMultiplier, if_neg hk]
    simp only [div_eq_mul_inv]
    ring

theorem angularDirichletVector_norm_sq {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) {z : ℂ} (hz : z ∈ U)
    (hp : Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi)) :
    ‖angularDirichletVector hU hf z‖ ^ 2 =
      (boundaryDSq (fun θ (_ : Unit) => f (z, θ))).toReal := by
  have hu := parameter_angle_slice_contDiff hf hz
  have hfin : boundaryDSq (fun θ (_ : Unit) => f (z, θ)) ≠ ⊤ := by
    apply boundaryDSq_ne_top_of_periodic_C1 (u' := deriv (fun θ => f (z, θ)))
    · intro θ
      exact (hu.differentiable (by simp) θ).hasDerivAt
    · exact hu.continuous_deriv (by simp)
    · simpa only [zero_add] using hp 0
  have heq : angularDirichletVector hU hf z = dirichletVector (fun θ => f (z, θ)) hfin := by
    apply Subtype.ext
    funext k
    exact angularDirichletVector_coeff hU hf hz hp k
  rw [heq, dirichletVector_norm_sq]

end Yau.Blueprint.V03Proof
