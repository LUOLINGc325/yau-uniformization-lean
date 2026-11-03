import Yau.Proofs.P04CoefficientChoice
import Mathlib.Analysis.Calculus.SmoothSeries

noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff

namespace Yau.Proofs.P04Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Genuine compact smooth functions supply every finite derivative budget. -/
theorem exists_global_derivative_budgets (b : ℕ → ℕ → E → ℝ)
    (hb : ∀ i j, ContDiff ℝ ∞ (b i j)) (hc : ∀ i j, HasCompactSupport (b i j)) :
    ∃ D : ℕ → ℕ → ℕ → ℝ, ∀ i j q, 0 ≤ D i j q ∧
      ∀ x, ‖iteratedFDeriv ℝ q (b i j) x‖ ≤ D i j q := by
  choose D hD0 hD using fun i j q => (hc i j).exists_bound_iteratedFDeriv (hb i j) q
  exact ⟨D,fun i j q => ⟨hD0 i j q,fun x => hD i j q q le_rfl x⟩⟩

/-- Select the coefficients only after all actual compact derivative budgets
exist, and obtain smooth global sums on every buffered coordinate model. -/
theorem exists_coefficients_with_smooth_sums (b : ℕ → ℕ → E → ℝ)
    (hb : ∀ i j, ContDiff ℝ ∞ (b i j)) (hcompact : ∀ i j, HasCompactSupport (b i j))
    (B : ℕ → ℝ) :
    ∃ c : ℕ → ℝ,
      (∀ i, 0 < c i ∧ c i*Real.exp (B i) ≤ (1/2 : ℝ)^i) ∧
      ∀ j, ContDiff ℝ ∞ (fun x => ∑' i, c i*b i j x) := by
  classical
  obtain ⟨D,hD⟩ := exists_global_derivative_budgets b hb hcompact
  obtain ⟨c,hc⟩ := exists_positive_diagonal_coefficients B D
  refine ⟨c,fun i => ⟨(hc i).1,(hc i).2.1⟩,fun j => ?_⟩
  apply contDiff_tsum_of_eventually (v := fun _ i => (1/2 : ℝ)^i)
  · intro i
    exact contDiff_const.mul (hb i j)
  · intro q _
    exact geometric_half_hasSum.summable
  · intro q _
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop (max j q)] with i hi
    intro x
    have hij : j ≤ i := (le_max_left j q).trans hi
    have hiq : q ≤ i := (le_max_right j q).trans hi
    have HH := (hc i).2.2 j hij q hiq
    rw [abs_of_nonneg (hD i j q).1] at HH
    have hderiv : iteratedFDeriv ℝ q (fun x => c i*b i j x) x =
        c i • iteratedFDeriv ℝ q (b i j) x :=
      by simpa only [smul_eq_mul] using
        (iteratedFDeriv_const_smul_apply' (a := c i) (i := q) (x := x)
          ((hb i j).of_le (by simp)).contDiffAt)
    rw [hderiv,norm_smul,Real.norm_eq_abs,abs_of_pos (hc i).1]
    exact (mul_le_mul_of_nonneg_left ((hD i j q).2 x) (hc i).1.le).trans HH

end Yau.Proofs.P04Aux
