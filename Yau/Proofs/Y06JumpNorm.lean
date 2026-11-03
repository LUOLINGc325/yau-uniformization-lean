import Yau.Proofs.Y01ChangeBounds
import Yau.Proofs.Y03Frames

/-! Polynomial jump bounds follow from the actual aligned changes and
unitary shared frames. No inverse jump is supplied independently. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof
open Yau.Proofs.Y01Aux
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

theorem matrix_operator_mul_le (A B : Herm n) :
    matOpNorm (A * B) ≤ matOpNorm A * matOpNorm B := by
  change ‖A * B‖ ≤ ‖A‖ * ‖B‖
  exact norm_mul_le A B

theorem alignedJump_norm_sum_bound
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) (L : Changes n) (k : ℕ) (hplus : IsUnit (L.plus k)) :
    matOpNorm (alignedJump E L k) + matOpNorm (alignedJump E L k)⁻¹ ≤
      (matOpNorm (L.plus k) + matOpNorm (L.plus k)⁻¹) *
        (matOpNorm (L.minus (k + 1)) + matOpNorm (L.minus (k + 1))⁻¹) := by
  have hjump := jump_unitary hE k
  have hinv : (jump E k)⁻¹ = (jump E k).conjTranspose := Matrix.inv_eq_left_inv hjump.1
  have hJ : matOpNorm (alignedJump E L k) ≤ matOpNorm (L.minus (k + 1)) * matOpNorm (L.plus k)⁻¹ := by
    apply (matrix_operator_mul_le (L.minus (k + 1) * jump E k) (L.plus k)⁻¹).trans_eq
    rw [matOpNorm_mul_unitary hjump]
  have hJi : matOpNorm (alignedJump E L k)⁻¹ ≤ matOpNorm (L.plus k) * matOpNorm (L.minus (k + 1))⁻¹ := by
    rw [alignedJump, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hplus), hinv, ← Matrix.mul_assoc]
    apply (matrix_operator_mul_le (L.plus k * (jump E k).conjTranspose) (L.minus (k + 1))⁻¹).trans_eq
    rw [matOpNorm_mul_unitary (Yau.Blueprint.Alignment.Y03Proof.unitary_conjTranspose hjump)]
  have hcross₁ : 0 ≤ matOpNorm (L.plus k) * matOpNorm (L.minus (k + 1)) :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hcross₂ : 0 ≤ matOpNorm (L.plus k)⁻¹ * matOpNorm (L.minus (k + 1))⁻¹ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

theorem regularJump_norm_sum_raw
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {Q : ℕ → ℝ} {N j₀ : ℕ} {M hm : ℝ}
    {w : ℕ → Fin n → ℝ} {L : Changes n} {C c : ℝ} (hc : 0 < c)
    (hL : ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      ChangeAt (diagonal F tk E) w (macroAt Q N M hm j₀) (macroClock hm) C c L k)
    (k : ℕ) (hk : Regular Q N M (macroAt Q N M hm j₀ k)) :
    let J := if Regular Q N M (macroAt Q N M hm j₀ (k + 1)) then alignedJump E L k else 1
    matOpNorm J + matOpNorm J⁻¹ ≤
      if Regular Q N M (macroAt Q N M hm j₀ (k + 1)) then
        (1 + (macroAt Q N M hm j₀ k : ℝ)) ^ C *
          ((n + 1 : ℝ) * ((1 + (macroAt Q N M hm j₀ (k + 1) : ℝ)) ^ C + 2) ^ (n + 1))
      else 2 := by
  dsimp only
  by_cases hnext : Regular Q N M (macroAt Q N M hm j₀ (k + 1))
  · simp only [ite_eq_left hnext]
    have hplus := (hL k hk).2.2.2.2.1
    have hminus := minus_change_polynomial_bound hE hc (hL (k + 1) hnext)
    apply (alignedJump_norm_sum_bound hE L k (plus_change_isUnit (hL k hk))).trans
    apply mul_le_mul hplus hminus
    · exact add_nonneg (norm_nonneg _) (norm_nonneg _)
    · positivity
  · simp only [ite_eq_right hnext, inv_one]
    have h := add_le_add (matOpNorm_one_le (n := n)) (matOpNorm_one_le (n := n))
    simpa only [one_add_one_eq_two] using h

end Yau.Proofs.Y06Aux
