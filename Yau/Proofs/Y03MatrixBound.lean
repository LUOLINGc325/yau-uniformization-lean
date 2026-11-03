import Yau.Proofs.Y03JointPullback

/-! Entry bounds control the actual Euclidean matrix operator norm. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem matOpNorm_le_sum_entries (A : Herm n) : matOpNorm A ≤ ∑ i, ∑ j, ‖A i j‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  intro x
  let y := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x
  have hnorm (i : Fin n) : ‖stdVec i‖ = 1 := by simp [stdVec, EuclideanSpace.single]
  have hcomponent (i : Fin n) : ‖y i‖ ≤ (∑ j, ‖A i j‖) * ‖x‖ := by
    change ‖∑ j, A i j * x j‖ ≤ _
    calc
      _ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖A i j‖ * ‖x‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) (norm_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    ‖y‖ = ‖∑ i, y i • stdVec i‖ := congrArg norm (sum_stdVec y).symm
    _ ≤ ∑ i, ‖y i • stdVec i‖ := norm_sum_le _ _
    _ = ∑ i, ‖y i‖ := by simp only [norm_smul, hnorm, mul_one]
    _ ≤ ∑ i, (∑ j, ‖A i j‖) * ‖x‖ := Finset.sum_le_sum fun i _ => hcomponent i
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem matOpNorm_le_card_sq_mul {A : Herm n} {B : ℝ} (_hB : 0 ≤ B)
    (hA : ∀ i j, ‖A i j‖ ≤ B) : matOpNorm A ≤ (n : ℝ) ^ 2 * B := by
  apply (matOpNorm_le_sum_entries A).trans
  calc
    (∑ i, ∑ j, ‖A i j‖) ≤ ∑ _i : Fin n, ∑ _j : Fin n, B :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hA i j
    _ = _ := by simp [pow_two, mul_assoc]

end Yau.Blueprint.Alignment.Y03Proof
