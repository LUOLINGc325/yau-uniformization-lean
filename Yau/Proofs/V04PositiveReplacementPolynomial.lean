import Yau.Blueprint.VariationContracts
import Mathlib.Analysis.Normed.Field.Lemmas

/-! A quantitative Lipschitz estimate for the actual finite polynomial.
Only its matrix entries are bounded; no norm is silently interchanged. -/
open scoped Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.PositiveReplacementAux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem bivectorCost_entry_lipschitz {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 ≤ Q) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (A B J : CotangentMatrix n),
      (∀ i j, ‖A i j‖ ≤ M) → (∀ i j, ‖B i j‖ ≤ M) →
      (∀ i j, ‖J i j‖ ≤ Q) → ∀ {D : ℝ}, 0 ≤ D →
      (∀ i j, ‖A i j - B i j‖ ≤ D) →
      |bivectorCost A J - bivectorCost B J| ≤ L * D := by
  classical
  let L : ℝ := (1 / 2 : ℝ) * ∑ _i : CotangentIndex n, ∑ _j : CotangentIndex n,
    ∑ _k : CotangentIndex n, ∑ _l : CotangentIndex n, (Q ^ 2 * (2 * M))
  refine ⟨L, mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ =>
      Finset.sum_nonneg (fun l _ => by positivity))))), ?_⟩
  intro A B J hA hB hJ D hD hdiff
  let P (A : CotangentMatrix n) : ℂ :=
    ∑ i, ∑ j, ∑ k, ∑ l, J i j * star (J k l) * A k i * A l j
  have hP : P A - P B = ∑ i, ∑ j, ∑ k, ∑ l,
      J i j * star (J k l) * (A k i * A l j - B k i * B l j) := by
    simp only [P, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hterm (i j k l : CotangentIndex n) :
      ‖J i j * star (J k l) * (A k i * A l j - B k i * B l j)‖ ≤
        Q ^ 2 * (2 * M) * D := by
    have hp : ‖A k i * A l j - B k i * B l j‖ ≤ 2 * M * D := by
      calc
        _ = ‖(A k i - B k i) * A l j + B k i * (A l j - B l j)‖ := by congr 1; ring
        _ ≤ ‖(A k i - B k i) * A l j‖ + ‖B k i * (A l j - B l j)‖ := norm_add_le _ _
        _ ≤ D * M + M * D := by
          simp only [norm_mul]
          exact add_le_add (mul_le_mul (hdiff k i) (hA l j) (norm_nonneg _) hD)
            (mul_le_mul (hB k i) (hdiff l j) (norm_nonneg _) hM)
        _ = _ := by ring
    have hJJ : ‖J i j * star (J k l)‖ ≤ Q ^ 2 := by
      rw [norm_mul, norm_star, pow_two]
      exact mul_le_mul (hJ i j) (hJ k l) (norm_nonneg _) hQ
    rw [norm_mul]
    calc
      _ ≤ Q ^ 2 * (2 * M * D) := mul_le_mul hJJ hp (norm_nonneg _) (sq_nonneg Q)
      _ = _ := by ring
  change |(1 / 2 : ℝ) * (P A).re - (1 / 2 : ℝ) * (P B).re| ≤ _
  rw [← mul_sub, ← Complex.sub_re, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * ‖P A - P B‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (∑ i : CotangentIndex n, ∑ j : CotangentIndex n,
        ∑ k : CotangentIndex n, ∑ l : CotangentIndex n, Q ^ 2 * (2 * M) * D) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [hP]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k _
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun l _ => hterm i j k l)
    _ = L * D := by dsimp only [L]; simp_rw [← Finset.sum_mul]; ring

end Yau.Blueprint.V04Proof.PositiveReplacementAux
