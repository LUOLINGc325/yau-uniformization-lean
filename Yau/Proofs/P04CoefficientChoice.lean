import Yau.Proofs.P04GrowthAlgebra

noncomputable section
open scoped BigOperators

namespace Yau.Proofs.P04Aux

/-- A single positive coefficient controls growth and every finite derivative
budget through its own index. The geometric budgets will be supplied by the
actual compact chart derivative bounds. -/
theorem exists_positive_diagonal_coefficients (B : ℕ → ℝ) (D : ℕ → ℕ → ℕ → ℝ) :
    ∃ c : ℕ → ℝ, ∀ i,
      0 < c i ∧ c i*Real.exp (B i) ≤ (1/2 : ℝ)^i ∧
      ∀ j ≤ i, ∀ q ≤ i, c i*|D i j q| ≤ (1/2 : ℝ)^i := by
  classical
  let T : ℕ → ℝ := fun i => ∑ j ∈ Finset.range (i+1), ∑ q ∈ Finset.range (i+1), |D i j q|
  let d : ℕ → ℝ := fun i => 1+Real.exp (B i)+T i
  have hT (i : ℕ) : 0 ≤ T i := Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun q _ => abs_nonneg _))
  have hd (i : ℕ) : 0 < d i := by dsimp only [d]; linarith [hT i,Real.exp_pos (B i)]
  have hde (i : ℕ) : Real.exp (B i) ≤ d i := by dsimp only [d];linarith [hT i]
  have hD (i j q : ℕ) (hj : j ≤ i) (hq : q ≤ i) : |D i j q| ≤ d i := by
    have Hq : |D i j q| ≤ ∑ l ∈ Finset.range (i+1), |D i j l| :=
      Finset.single_le_sum (f := fun l : ℕ => |D i j l|) (s := Finset.range (i+1)) (a := q) (fun l _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
    have Hj : (∑ l ∈ Finset.range (i+1), |D i j l|) ≤ T i :=
      Finset.single_le_sum (f := fun l : ℕ => ∑ m ∈ Finset.range (i+1), |D i l m|) (s := Finset.range (i+1)) (a := j) (fun l _ => Finset.sum_nonneg (fun q _ => abs_nonneg _))
        (Finset.mem_range.mpr (by omega))
    have H := Hq.trans Hj
    dsimp only [d]
    linarith [Real.exp_pos (B i)]
  let c : ℕ → ℝ := fun i => (1/2 : ℝ)^i/d i
  have hmul (i : ℕ) (x : ℝ) (hx : x ≤ d i) : c i*x ≤ (1/2 : ℝ)^i := by
    calc
      c i*x ≤ c i*d i := mul_le_mul_of_nonneg_left hx (by dsimp only [c]; exact div_nonneg (pow_nonneg (by norm_num) _) (hd i).le)
      _ = _ := by dsimp only [c];exact div_mul_cancel₀ _ (hd i).ne'
  exact ⟨c,fun i => ⟨by dsimp only [c]; exact div_pos (pow_pos (by norm_num) _) (hd i),hmul i _ (hde i),
    fun j hj q hq => hmul i _ (hD i j q hj hq)⟩⟩

end Yau.Proofs.P04Aux
