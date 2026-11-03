import Yau.Proofs.V03ReciprocalLevi

/-! Scalar derivative formulas for the actual reciprocal wall. Inversion
is differentiated only where the original profile is nonzero. -/

open Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
set_option backward.isDefEq.respectTransparency false

def wallScalar (p : ℝ → ℝ) (A : ℝ) (u : ℝ) : ℝ := (p (u / A))⁻¹ - 1

theorem wallScalar_hasDerivAt {p : ℝ → ℝ} {A u : ℝ}
    (hp : DifferentiableAt ℝ p (u / A)) (hne : p (u / A) ≠ 0) :
    HasDerivAt (wallScalar p A) (-(deriv p (u / A) / A) / p (u / A) ^ 2) u := by
  have h := ((hp.hasDerivAt.comp u ((hasDerivAt_id u).div_const A)).inv hne).sub_const 1
  convert! h using 1 <;> simp only [wallScalar, Function.comp_def, id_eq, mul_one_div, Pi.inv_apply]

theorem wallScalar_deriv {p : ℝ → ℝ} {A u : ℝ}
    (hp : DifferentiableAt ℝ p (u / A)) (hne : p (u / A) ≠ 0) :
    deriv (wallScalar p A) u = -(deriv p (u / A) / A) / p (u / A) ^ 2 :=
  (wallScalar_hasDerivAt hp hne).deriv

theorem wallScalar_secondDeriv {p : ℝ → ℝ} (hp : ContDiff ℝ ∞ p)
    {A u : ℝ} (hA : A ≠ 0) (hne : p (u / A) ≠ 0) :
    deriv (deriv (wallScalar p A)) u =
      2 * (deriv p (u / A) / A) ^ 2 / p (u / A) ^ 3 -
        (deriv (deriv p) (u / A) / A ^ 2) / p (u / A) ^ 2 := by
  have hd : Differentiable ℝ p := hp.differentiable (by simp)
  have hd' : Differentiable ℝ (deriv p) :=
    (contDiff_infty_iff_deriv.mp hp).2.differentiable (by simp)
  have hq := (hd (u / A)).hasDerivAt.comp u ((hasDerivAt_id u).div_const A)
  have hq' := (hd' (u / A)).hasDerivAt.comp u ((hasDerivAt_id u).div_const A)
  have heq : deriv (wallScalar p A) =ᶠ[𝓝 u]
      (fun v => -(deriv p (v / A) / A) / p (v / A) ^ 2) := by
    filter_upwards [((hp.continuous.comp (continuous_id.div_const A)).continuousAt.eventually_ne hne)]
      with v hv
    exact wallScalar_deriv (hd (v / A)) hv
  rw [heq.deriv_eq]
  have hquot := ((hq'.div_const A).neg).div (hq.pow 2) (pow_ne_zero 2 hne)
  have hv := hquot.deriv
  simp only [Function.comp_def, id_eq, mul_one_div, Pi.pow_apply, Pi.neg_apply] at hv
  change deriv (fun v => -(deriv p (v / A) / A) / p (v / A) ^ 2) u = _ at hv
  rw [hv]
  field_simp [hA, hne]
  <;> ring

theorem profile_two_derivatives_bound {p : ℝ → ℝ} (hp : ContDiff ℝ ∞ p) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ r ∈ Set.Icc (0 : ℝ) 1,
      |deriv p r| ≤ M ∧ |deriv (deriv p) r| ≤ M := by
  have hp' : ContDiff ℝ ∞ (deriv p) := (contDiff_infty_iff_deriv.mp hp).2
  have hp'' : ContDiff ℝ ∞ (deriv (deriv p)) := (contDiff_infty_iff_deriv.mp hp').2
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hp'.continuous.continuousOn
  obtain ⟨M₂, hM₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hp''.continuous.continuousOn
  refine ⟨1 + |M₁| + |M₂|, by linarith [abs_nonneg M₁, abs_nonneg M₂], fun r hr => ?_⟩
  have h₁ := hM₁ r hr
  have h₂ := hM₂ r hr
  simp only [Real.norm_eq_abs] at h₁ h₂
  constructor <;> nlinarith [le_abs_self M₁, le_abs_self M₂, abs_nonneg M₁, abs_nonneg M₂]

end Yau.Blueprint.V04Proof.WallErrorAux
