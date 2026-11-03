import Yau.Proofs.Y06ForbiddenProjection

/-! The diagonal coefficient factor in terms of the original logarithmic
rates, and the scalar clock estimate used for every incoming coefficient. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment

variable {n : ℕ}

theorem inverse_prod_eq_exp_logs (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (i : Fin n) (β : Fin n →₀ ℕ) :
    (a i)⁻¹ * ∏ j ∈ β.support, a j ^ β j =
      Real.exp ((∑ j ∈ β.support, (β j : ℝ) * Real.log (a j)) - Real.log (a i)) := by
  classical
  have hprod : Real.exp (∑ j ∈ β.support, (β j : ℝ) * Real.log (a j)) =
      ∏ j ∈ β.support, a j ^ β j := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Real.exp_nat_mul, Real.exp_log (ha j)]
  rw [Real.exp_sub, hprod, Real.exp_log (ha i)]
  ring

theorem inverse_prod_eq_exp_rate_gap (a μ : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    {τ : ℝ} (hτ : 0 < τ) (hμ : ∀ i, μ i = -2 * Real.log (a i) / τ)
    (i : Fin n) (β : Fin n →₀ ℕ) :
    (a i)⁻¹ * ∏ j ∈ β.support, a j ^ β j =
      Real.exp (-τ * ((∑ j, (β j : ℝ) * μ j) - μ i) / 2) := by
  classical
  rw [inverse_prod_eq_exp_logs a ha]
  have hlogs j : Real.log (a j) = (-τ / 2) * μ j := by
    rw [hμ j]
    field_simp
  have hsupport : (∑ j ∈ β.support, (β j : ℝ) * Real.log (a j)) =
      ∑ j, (β j : ℝ) * Real.log (a j) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j hj hnot
    rw [Finsupp.notMem_support_iff.mp hnot]
    simp
  have hsum : (∑ j, (β j : ℝ) * ((-τ / 2) * μ j)) =
      (-τ / 2) * ∑ j, (β j : ℝ) * μ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  apply congrArg Real.exp
  rw [hsupport]
  simp_rw [hlogs]
  rw [hsum]
  ring

theorem clock_gap_exponent {τ total Δs Q A κ ch s gap j : ℝ}
    (hτ : 0 < τ) (hA : 0 < A) (hκ : 0 ≤ κ) (hj : 0 < j)
    (htrace : τ * total = Δs) (hupper : total ≤ A * Q)
    (hlower : ch * Real.sqrt s ≤ Δs) (hgap : κ * Q / j ^ 2 ≤ gap) :
    -τ * gap / 2 ≤ -(κ * ch / (2 * A)) * Real.sqrt s / j ^ 2 := by
  have hj2 : 0 < j ^ 2 := sq_pos_of_pos hj
  have hclock : ch * Real.sqrt s ≤ A * τ * Q := by
    calc
      _ ≤ Δs := hlower
      _ = τ * total := htrace.symm
      _ ≤ τ * (A * Q) := mul_le_mul_of_nonneg_left hupper hτ.le
      _ = _ := by ring
  have hg : κ * Q ≤ gap * j ^ 2 := (div_le_iff₀ hj2).mp hgap
  have hh : κ * ch * Real.sqrt s ≤ A * τ * gap * j ^ 2 := by
    calc
      _ = κ * (ch * Real.sqrt s) := by ring
      _ ≤ κ * (A * τ * Q) := mul_le_mul_of_nonneg_left hclock hκ
      _ = (A * τ) * (κ * Q) := by ring
      _ ≤ (A * τ) * (gap * j ^ 2) := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by ring
  have hratio : κ * ch * Real.sqrt s / (2 * A * j ^ 2) ≤ τ * gap / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * A * j ^ 2)).mpr
    nlinarith [hh]
  calc
    _ ≤ -(κ * ch * Real.sqrt s / (2 * A * j ^ 2)) := by linarith
    _ = _ := by field_simp

theorem diagonal_factor_clock_bound (a μ : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    {τ Δs Q A κ ch s j : ℝ} (hτ : 0 < τ) (hA : 0 < A) (hκ : 0 ≤ κ) (hj : 0 < j)
    (hμ : ∀ i, μ i = -2 * Real.log (a i) / τ)
    (htrace : τ * (∑ l, μ l) = Δs) (hupper : (∑ l, μ l) ≤ A * Q)
    (hlower : ch * Real.sqrt s ≤ Δs) (i : Fin n) (β : Fin n →₀ ℕ)
    (hgap : κ * Q / j ^ 2 ≤ (∑ l, (β l : ℝ) * μ l) - μ i) :
    (a i)⁻¹ * ∏ l ∈ β.support, a l ^ β l ≤
      Real.exp (-(κ * ch / (2 * A)) * Real.sqrt s / j ^ 2) := by
  rw [inverse_prod_eq_exp_rate_gap a μ ha hτ hμ]
  exact Real.exp_le_exp.mpr (clock_gap_exponent hτ hA hκ hj htrace hupper hlower hgap)

end Yau.Proofs.Y06Aux
