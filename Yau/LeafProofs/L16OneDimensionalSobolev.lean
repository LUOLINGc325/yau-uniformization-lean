import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith

/-!
# A global one-dimensional Sobolev evaluation estimate

The estimates here concern actual compactly supported `C¹` real functions and their
ordinary derivatives, with integration against Lebesgue volume.
-/

namespace Yau.LeafProofs.L16Aux

open MeasureTheory Set

set_option backward.isDefEq.respectTransparency.types false

/-- A compactly supported `C¹` real function is square-integrable. -/
theorem integrable_sq_of_contDiff_one_hasCompactSupport {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) :
    Integrable (fun s ↦ (f s) ^ 2) := by
  have hcs : HasCompactSupport (fun s ↦ (f s) ^ 2) :=
    hcf.comp_left (g := fun x : ℝ ↦ x ^ 2) (by simp)
  have hcont : Continuous (fun s ↦ (f s) ^ 2) := hf.continuous.pow 2
  exact hcont.integrable_of_hasCompactSupport hcs

/-- The ordinary derivative of a compactly supported `C¹` real function is
square-integrable. -/
theorem integrable_deriv_sq_of_contDiff_one_hasCompactSupport {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) :
    Integrable (fun s ↦ (deriv f s) ^ 2) := by
  have hcs : HasCompactSupport (fun s ↦ (deriv f s) ^ 2) :=
    hcf.deriv.comp_left (g := fun x : ℝ ↦ x ^ 2) (by simp)
  have hcont : Continuous (fun s ↦ (deriv f s) ^ 2) :=
    (hf.continuous_deriv le_rfl).pow 2
  exact hcont.integrable_of_hasCompactSupport hcs

/-- Global Sobolev evaluation bound, with constant one, for compactly supported
`C¹` real functions. -/
theorem sq_le_integral_sq_add_integral_deriv_sq {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) (t : ℝ) :
    (f t) ^ 2 ≤ (∫ s, (f s) ^ 2) + ∫ s, (deriv f s) ^ 2 := by
  have hfi := integrable_sq_of_contDiff_one_hasCompactSupport hf hcf
  have hdi := integrable_deriv_sq_of_contDiff_one_hasCompactSupport hf hcf
  have hq : ContDiff ℝ 1 (fun s ↦ (f s) ^ 2) := hf.pow 2
  have hcq : HasCompactSupport (fun s ↦ (f s) ^ 2) :=
    hcf.comp_left (g := fun x : ℝ ↦ x ^ 2) (by simp)
  have hder : deriv (fun s ↦ (f s) ^ 2) = fun s ↦ 2 * f s * deriv f s := by
    funext s
    simpa using ((hf.differentiable one_ne_zero s).hasDerivAt.fun_pow 2).deriv
  have hqi : Integrable (fun s ↦ 2 * f s * deriv f s) := by
    rw [← hder]
    exact (hq.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcq.deriv
  have hftc : ∫ s in Iic t, 2 * f s * deriv f s = (f t) ^ 2 := by
    rw [← hder]
    exact HasCompactSupport.integral_Iic_deriv_eq hq hcq t
  calc
    (f t) ^ 2 = ∫ s in Iic t, 2 * f s * deriv f s := hftc.symm
    _ ≤ ∫ s in Iic t, ((f s) ^ 2 + (deriv f s) ^ 2) := by
      apply integral_mono hqi.integrableOn (hfi.add hdi).integrableOn
      intro s
      change 2 * f s * deriv f s ≤ (f s) ^ 2 + (deriv f s) ^ 2
      nlinarith [sq_nonneg (f s - deriv f s)]
    _ ≤ ∫ s, ((f s) ^ 2 + (deriv f s) ^ 2) := by
      exact setIntegral_le_integral (hfi.add hdi)
        (Filter.Eventually.of_forall (fun s ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)))
    _ = (∫ s, (f s) ^ 2) + ∫ s, (deriv f s) ^ 2 := integral_add hfi hdi

/-- The evaluation estimate for a difference uses the actual derivatives of the
two functions. -/
theorem sub_sq_le_integral_sub_sq_add_integral_deriv_sub_sq {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f)
    (hg : ContDiff ℝ 1 g) (hcg : HasCompactSupport g) (t : ℝ) :
    (f t - g t) ^ 2 ≤ (∫ s, (f s - g s) ^ 2) +
      ∫ s, (deriv f s - deriv g s) ^ 2 := by
  have hsub : ContDiff ℝ 1 (fun s ↦ f s - g s) := hf.sub hg
  have hcsub : HasCompactSupport (fun s ↦ f s - g s) := hcf.sub hcg
  have hdsub : deriv (fun s ↦ f s - g s) = fun s ↦ deriv f s - deriv g s := by
    funext s
    exact deriv_fun_sub (hf.differentiable one_ne_zero s) (hg.differentiable one_ne_zero s)
  simpa only [hdsub] using sq_le_integral_sq_add_integral_deriv_sq hsub hcsub t

/-- Cauchy control of the squared `L²` differences of functions and their first
derivatives implies uniform Cauchy control of the actual functions. -/
theorem uniform_cauchy_of_integral_sq_cauchy {f : ℕ → ℝ → ℝ}
    (hf : ∀ k, ContDiff ℝ 1 (f k)) (hcf : ∀ k, HasCompactSupport (f k))
    (hcauchy : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N,
      (∫ s, (f k s - f l s) ^ 2) +
        (∫ s, (deriv (f k) s - deriv (f l) s) ^ 2) < δ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ t : ℝ,
      |f k t - f l t| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hcauchy (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun k hk l hl t ↦ ?_⟩
  have hbound := sub_sq_le_integral_sub_sq_add_integral_deriv_sub_sq
    (hf k) (hcf k) (hf l) (hcf l) t
  have hsquare : (f k t - f l t) ^ 2 < ε ^ 2 := hbound.trans_lt (hN k hk l hl)
  exact (sq_lt_sq₀ (abs_nonneg _) hε.le).mp (by simpa only [sq_abs] using hsquare)

end Yau.LeafProofs.L16Aux
