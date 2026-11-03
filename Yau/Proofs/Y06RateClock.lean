import Yau.Proofs.Y06BackwardContraction
import Yau.Proofs.Y03Frames

/-! The trace and inverse diagonal bounds follow from the original SVD and
determinant clock, rather than additional geometric assumptions. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

theorem derivative_matrix_det_clock
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk s : ℕ → ℝ}
    (hdet : ∀ k, ‖transitionDet F (tk k) (tk (k + 1)) 0‖ = Real.exp (-(s (k + 1) - s k) / 2)) :
    ∀ k, ‖(derivativeMatrix (F (tk k) (tk (k + 1)))).det‖ =
      Real.exp (-(s (k + 1) - s k) / 2) := by
  intro k
  rw [derivativeMatrix_det]
  exact hdet k

theorem original_rate_clock_identity
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk s : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E)
    (hdet : ∀ k, ‖transitionDet F (tk k) (tk (k + 1)) 0‖ = Real.exp (-(s (k + 1) - s k) / 2))
    (k : ℕ) : Real.log (tk (k + 1) / tk k) * (∑ i, rate F tk E k i) = s (k + 1) - s k := by
  rw [trace_rate_of_det hE (derivative_matrix_det_clock hdet) k]
  have hτ := log_time_ratio_pos (hE k).1 (hE k).2.1
  field_simp

theorem original_singular_product_clock
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk s : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E)
    (hdet : ∀ k, ‖transitionDet F (tk k) (tk (k + 1)) 0‖ = Real.exp (-(s (k + 1) - s k) / 2))
    (k : ℕ) : (∏ i, singularLength F tk E k i) = Real.exp (-(s (k + 1) - s k) / 2) :=
  (product_singularLength_eq_norm_det hE k).trans (derivative_matrix_det_clock hdet k)

theorem singular_inverse_clock_bound
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk s : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E)
    (hdet : ∀ k, ‖transitionDet F (tk k) (tk (k + 1)) 0‖ = Real.exp (-(s (k + 1) - s k) / 2))
    (k : ℕ) (i : Fin n) : (singularLength F tk E k i)⁻¹ ≤ Real.exp ((s (k + 1) - s k) / 2) := by
  have hprod : (∏ j, singularLength F tk E k j) ≤ singularLength F tk E k i := by
    have h := Finset.prod_le_prod_of_subset_of_le_one₀
      (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
      (fun j hj => ((hE k).2.2.2.2.2.1 j).1.le)
      (fun j hj hnot => ((hE k).2.2.2.2.2.1 j).2)
    simpa only [Finset.prod_singleton] using h
  rw [original_singular_product_clock hE hdet k] at hprod
  have hle := one_div_le_one_div_of_le (Real.exp_pos _) hprod
  have hexp : (Real.exp (-(s (k + 1) - s k) / 2))⁻¹ = Real.exp ((s (k + 1) - s k) / 2) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  simpa only [one_div, hexp] using hle

theorem diagonal_inverse_clock_bound
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk s : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E)
    (hdet : ∀ k, ‖transitionDet F (tk k) (tk (k + 1)) 0‖ = Real.exp (-(s (k + 1) - s k) / 2))
    (k : ℕ) : matOpNorm (diagonal F tk E k)⁻¹ ≤ Real.exp ((s (k + 1) - s k) / 2) := by
  have hinv : (diagonal F tk E k)⁻¹ =
      Matrix.diagonal (fun i => (singularLength F tk E k i : ℂ)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    unfold diagonal
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt ((hE k).2.2.2.2.2.1 i).1))
  change ‖(diagonal F tk E k)⁻¹‖ ≤ _
  rw [hinv, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr
  intro i
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ((hE k).2.2.2.2.2.1 i).1]
  exact singular_inverse_clock_bound hE hdet k i

theorem rate_weight_backward_bound
    (hn : 0 < n) {Q : ℕ → ℝ} {N j₀ : ℕ} {M hm scale K eps b : ℝ} (hb : 0 < b)
    (hgrid : GridLayout Q N M hm j₀)
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E)
    (hdet : ∀ k, ‖transitionDet F (tk k) (tk (k + 1)) 0‖ =
      Real.exp (-(gridClock Q N M hm j₀ (k + 1) - gridClock Q N M hm j₀ k) / 2))
    (hweights : WeightEstimates Q N M hm scale K eps b j₀ (rate F tk E)) :
    ∃ c : ℝ, 0 < c ∧ ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      0 < macroAt Q N M hm j₀ k → ∀ (J : Herm n) (m : ℕ), 2 ≤ m →
        ∀ P : PolyMap n, Homogeneous P m →
          (backwardOperator (diagonal F tk E k) J
            (weight Q N M hm scale K eps j₀ (rate F tk E) k) P).coeffNorm ≤
            (Real.exp (-c * Real.sqrt (gridClock Q N M hm j₀ k) / (macroAt Q N M hm j₀ k : ℝ) ^ 2) *
              (∑ i, ∑ l, ‖J⁻¹ i l‖) * (1 + (linearPolynomial J).coeffNorm) ^ m) * P.coeffNorm := by
  obtain ⟨ch, Ch, hch, hCh, hsteps⟩ := hgrid.2.2.2.2.2
  let A : ℝ := (n : ℝ) * b⁻¹
  have hA : 0 < A := mul_pos (by exact_mod_cast hn) (inv_pos.mpr hb)
  refine ⟨0.8 * ch / (2 * A), by positivity, ?_⟩
  intro k hk hj J m hm2 P hP
  have hupper : (∑ i, rate F tk E k i) ≤ A * Q (macroAt Q N M hm j₀ k) := by
    calc
      _ ≤ ∑ i : Fin n, b⁻¹ * Q (macroAt Q N M hm j₀ k) :=
        Finset.sum_le_sum (fun i hi => (hweights.1 k i hk).2.1)
      _ = _ := by simp [A]; ring
  apply backwardOperator_clock_bound (singularLength F tk E k) (rate F tk E k)
    (fun i => ((hE k).2.2.2.2.2.1 i).1) J _ hP
    (log_time_ratio_pos (hE k).1 (hE k).2.1) hA (by norm_num)
    (by exact_mod_cast hj) (fun i => rfl) (original_rate_clock_identity hE hdet k) hupper (hsteps k).1
  intro i β hdegree hforbidden
  have hgap := (hweights.2.2.1 k i β hk (by omega) hforbidden).le
  simpa only [theta, mul_div_assoc] using hgap

end Yau.Proofs.Y06Aux
