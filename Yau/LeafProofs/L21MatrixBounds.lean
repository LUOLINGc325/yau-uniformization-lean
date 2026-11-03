import Yau.LeafProofs.L21Normalization

/-! Dimension-dependent bounds relating the actual entrywise finite jet
normalization to the Hermitian Euclidean operator norm. -/

noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem euclidean_norm_le_sum_coordinates (v : X n) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
  calc
    _ = ‖∑ i, v i • Yau.stdVec i‖ := congrArg norm (sum_stdVec v).symm
    _ ≤ ∑ i, ‖v i • Yau.stdVec i‖ := norm_sum_le _ _
    _ = _ := by simp [norm_smul, Yau.stdVec]

theorem matrixOpNorm_le_entry_bound (A : Matrix (Fin n) (Fin n) ℂ) {b : ℝ}
    (hb : 0 ≤ b) (hA : ∀ i j, ‖A i j‖ ≤ b) :
    Yau.LeafCandidates.matrixOpNorm A ≤ (n : ℝ) ^ 2 * b := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hrow (i : Fin n) :
      ‖(Matrix.toEuclideanLin A).toContinuousLinearMap v i‖ ≤ (n : ℝ) * b * ‖v‖ := by
    change ‖∑ j, A i j * v j‖ ≤ _
    calc
      _ ≤ ∑ j, ‖A i j * v j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, b * ‖v‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul (hA i j) (PiLp.norm_apply_le v j) (norm_nonneg _) hb
      _ = _ := by simp; ring
  calc
    _ ≤ ∑ i, ‖(Matrix.toEuclideanLin A).toContinuousLinearMap v i‖ :=
      euclidean_norm_le_sum_coordinates _
    _ ≤ ∑ _i : Fin n, (n : ℝ) * b * ‖v‖ := Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by simp; ring

theorem jetBound_zero_matrixOpNorm {O : Set (X n)}
    {A : X n → Matrix (Fin n) (Fin n) ℂ} {b : ℝ} (hb : 0 ≤ b) {q : ℕ}
    (hA : JetBound q b A O) (x : X n) (hx : x ∈ O) :
    Yau.LeafCandidates.matrixOpNorm (A x) ≤ (n : ℝ) ^ 2 * b := by
  apply matrixOpNorm_le_entry_bound (A x) hb
  intro i j
  simpa only [norm_iteratedFDeriv_zero] using hA 0 (Nat.zero_le q) x hx i j

theorem jetBound_small_matrixOpNorm {O : Set (X n)}
    {A : X n → Matrix (Fin n) (Fin n) ℂ} {q : ℕ}
    (hA : JetBound q (1 / (2 * ((n : ℝ) ^ 2 + 1))) A O) (x : X n) (hx : x ∈ O) :
    Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2 := by
  have hd : 0 < 2 * ((n : ℝ) ^ 2 + 1) := by positivity
  have hh := jetBound_zero_matrixOpNorm (one_div_nonneg.mpr (le_of_lt hd)) hA x hx
  apply hh.trans
  rw [mul_one_div, div_le_iff₀ hd]
  nlinarith [sq_nonneg (n : ℝ)]

end Yau.LeafProofs.L21Aux
