import Yau.Proofs.Y05Jacobian
import Yau.Proofs.Y05Logarithm
import Yau.Proofs.Y05LogJetBounds

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment Set
open scoped ContDiff

variable {n : ℕ}

def transitionDetBound (n : ℕ) (r M : ℝ) : ℝ :=
  max 1 ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (4 * M / r) ^ n)

theorem transitionDetBound_pos (n : ℕ) (r M : ℝ) : 0 < transitionDetBound n r M :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem norm_jacobian_det_on_half_ball {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    {f : ComplexVector n → ComplexVector n}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    (hb : ∀ z ∈ Metric.ball (0 : ComplexVector n) r, ‖f z‖ ≤ M) :
    ∀ z ∈ Metric.ball (0 : ComplexVector n) (r / 2),
      ‖LinearMap.det (fderiv ℂ f z).toLinearMap‖ ≤ transitionDetBound n r M := by
  intro z hz
  have hsub : Metric.ball z (r / 2) ⊆ Metric.ball (0 : ComplexVector n) r := by
    intro w hw
    have H := Metric.mem_ball.mp hz
    exact Metric.mem_ball.mpr ((dist_triangle w z 0).trans_lt (by
      have := Metric.mem_ball.mp hw
      linarith))
  have hD := U02AnalyticAux.norm_fderiv_le_two_mul_div_of_bound
    (by positivity : 0 < r / 2) hM (hf.mono hsub) (fun w hw => hb w (hsub hw))
  have hD' : ‖fderiv ℂ f z‖ ≤ 4 * M / r := by
    convert hD using 1 <;> ring
  apply (norm_linearMap_det_le (fderiv ℂ f z)).trans
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hD' n) (Nat.cast_nonneg _)).trans (le_max_right _ _)

/-- The logarithm is chosen on one fixed ball. Its real part has the
linear dependence on the actual volume-clock increment. -/
theorem exists_transition_log {r M Δ : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    {f : ComplexVector n → ComplexVector n}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    (hb : ∀ z ∈ Metric.ball (0 : ComplexVector n) r, ‖f z‖ ≤ M)
    (hinv : ∀ z ∈ Metric.ball (0 : ComplexVector n) r,
      Function.Bijective (fderiv ℂ f z))
    (hcenter : ‖LinearMap.det (fderiv ℂ f 0).toLinearMap‖ = Real.exp (-Δ / 2)) :
    ∃ P : ComplexVector n → ℂ,
      P 0 = 0 ∧ DifferentiableOn ℂ P (Metric.ball 0 (r / 2)) ∧
      (∀ z ∈ Metric.ball (0 : ComplexVector n) (r / 2),
        Complex.exp (P z) = LinearMap.det (fderiv ℂ f z).toLinearMap /
          LinearMap.det (fderiv ℂ f 0).toLinearMap) ∧
      ∀ z ∈ Metric.ball (0 : ComplexVector n) (r / 2),
        (P z).re ≤ Real.log (transitionDetBound n r M) + Δ / 2 := by
  let D : ComplexVector n → ℂ := fun z => LinearMap.det (fderiv ℂ f z).toLinearMap
  have hne (z : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) r) :
      D z ≠ 0 := jacobian_det_ne_zero (hinv z hz)
  have hD0 : D 0 ≠ 0 := hne 0 (Metric.mem_ball_self hr)
  have hD := differentiableOn_jacobian_det Metric.isOpen_ball hf
  have hg : DifferentiableOn ℂ (fun z => D z / D 0) (Metric.ball 0 r) := by
    convert! hD.mul_const (D 0)⁻¹ using 1
  obtain ⟨P, hP0, hP, hExp⟩ := exists_normalized_holomorphic_log hr hg
    (div_self hD0) (fun z hz => div_ne_zero (hne z hz) hD0)
  have hsub : Metric.ball (0 : ComplexVector n) (r / 2) ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (by linarith)
  refine ⟨P, hP0, hP.mono hsub, fun z hz => hExp z (hsub hz), ?_⟩
  intro z hz
  apply Real.exp_le_exp.mp
  rw [← Complex.norm_exp, hExp z (hsub hz), norm_div]
  change ‖D z‖ / ‖D 0‖ ≤ _
  have hEq : Real.exp (Real.log (transitionDetBound n r M) + Δ / 2) =
      transitionDetBound n r M / Real.exp (-Δ / 2) := by
    rw [Real.exp_add, Real.exp_log (transitionDetBound_pos n r M),
      show -Δ / 2 = -(Δ / 2) by ring, Real.exp_neg, div_inv_eq_mul]
  rw [hEq, hcenter]
  exact div_le_div_of_nonneg_right
    (norm_jacobian_det_on_half_ball hr hM hf hb z hz) (Real.exp_pos _).le

end Yau.Proofs.Y05Aux
