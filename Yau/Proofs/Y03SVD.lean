import Yau.Blueprint.Alignment

/-! Matrix and logarithmic identities for the actual singular frames in Y03. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem norm_det_unitary {A : Herm n} (hA : Unitary A) : ‖A.det‖ = 1 := by
  have hd := congrArg Matrix.det hA.1
  have hn := congrArg norm hd
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, norm_mul,
    norm_star, norm_one] at hn
  nlinarith [norm_nonneg A.det]

theorem unitary_conjTranspose {A : Herm n} (hA : Unitary A) : Unitary A.conjTranspose := by
  simpa only [Unitary, Matrix.conjTranspose_conjTranspose] using hA.symm

theorem unitary_mul {A B : Herm n} (hA : Unitary A) (hB : Unitary B) : Unitary (A * B) := by
  constructor
  · rw [Matrix.conjTranspose_mul]
    calc
      B.conjTranspose * A.conjTranspose * (A * B) =
          B.conjTranspose * (A.conjTranspose * A) * B := by noncomm_ring
      _ = 1 := by rw [hA.1, Matrix.mul_one, hB.1]
  · rw [Matrix.conjTranspose_mul]
    calc
      A * B * (B.conjTranspose * A.conjTranspose) =
          A * (B * B.conjTranspose) * A.conjTranspose := by noncomm_ring
      _ = 1 := by rw [hB.2, Matrix.mul_one, hA.2]

theorem jump_unitary {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E) (k : ℕ) :
    Unitary (jump E k) := by
  exact unitary_mul (unitary_conjTranspose (hE (k + 1)).2.2.1) (hE k).2.2.2.1

theorem log_time_ratio_pos {tk : ℕ → ℝ} {k : ℕ} (hpos : 0 < tk k)
    (hinc : tk k < tk (k + 1)) : 0 < Real.log (tk (k + 1) / tk k) := by
  apply Real.log_pos
  exact (one_lt_div hpos).2 hinc

theorem rate_nonneg {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E) (k : ℕ) (i : Fin n) :
    0 ≤ rate F tk E k i := by
  have hki := (hE k).2.2.2.2.2.1 i
  unfold rate
  apply div_nonneg
  · have := Real.log_nonpos hki.1.le hki.2
    linarith
  · exact (log_time_ratio_pos (hE k).1 (hE k).2.1).le

theorem rate_monotone_index {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E) (k : ℕ) :
    Monotone (rate F tk E k) := by
  intro i l hil
  have hσ := (hE k).2.2.2.2.2.2 hil
  have hlog := Real.log_le_log ((hE k).2.2.2.2.2.1 l).1 hσ
  unfold rate
  exact div_le_div_of_nonneg_right (by linarith) (log_time_ratio_pos (hE k).1 (hE k).2.1).le

theorem singularLength_eq_exp_rate {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E) (k : ℕ) (i : Fin n) :
    singularLength F tk E k i =
      Real.exp (-rate F tk E k i * Real.log (tk (k + 1) / tk k) / 2) := by
  have hT := ne_of_gt (log_time_ratio_pos (hE k).1 (hE k).2.1)
  have hσ := ((hE k).2.2.2.2.2.1 i).1
  unfold rate
  have heq : -(-2 * Real.log (singularLength F tk E k i) /
      Real.log (tk (k + 1) / tk k)) * Real.log (tk (k + 1) / tk k) / 2 =
        Real.log (singularLength F tk E k i) := by field_simp
  rw [heq, Real.exp_log hσ]

theorem norm_det_transformedDerivative
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) (k : ℕ) :
    ‖(transformedDerivative F tk E k).det‖ =
      ‖(derivativeMatrix (F (tk k) (tk (k + 1)))).det‖ := by
  unfold transformedDerivative
  rw [Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul,
    Matrix.det_conjTranspose, norm_star,
    norm_det_unitary (hE k).2.2.2.1, norm_det_unitary (hE k).2.2.1,
    one_mul, mul_one]

theorem product_singularLength_eq_norm_det
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) (k : ℕ) :
    (∏ i, singularLength F tk E k i) =
      ‖(derivativeMatrix (F (tk k) (tk (k + 1)))).det‖ := by
  rw [← norm_det_transformedDerivative hE k, (hE k).2.2.2.2.1]
  simp only [diagonal, Matrix.det_diagonal, norm_prod, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ((hE k).2.2.2.2.2.1 _).1]

theorem trace_rate_of_det
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk s : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E)
    (hdet : ∀ k, ‖(derivativeMatrix (F (tk k) (tk (k + 1)))).det‖ =
      Real.exp (-(s (k + 1) - s k) / 2)) (k : ℕ) :
    ∑ i, rate F tk E k i = (s (k + 1) - s k) / Real.log (tk (k + 1) / tk k) := by
  have hprod := product_singularLength_eq_norm_det hE k
  rw [hdet k] at hprod
  have hlog := congrArg Real.log hprod
  rw [Real.log_prod (fun i _ => ne_of_gt ((hE k).2.2.2.2.2.1 i).1), Real.log_exp] at hlog
  unfold rate
  rw [← Finset.sum_div, ← Finset.mul_sum, hlog]
  congr 1
  ring

end Yau.Blueprint.Alignment.Y03Proof
