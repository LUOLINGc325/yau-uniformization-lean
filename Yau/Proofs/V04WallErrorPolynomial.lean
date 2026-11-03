import Yau.Proofs.V04WallErrorAlgebra

/-! Quadratic and bilinear identities for the actual symplectic polynomial. -/

open scoped Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau
variable {n : ℕ}

def symplecticCross (W K : CotangentMatrix n) : ℝ :=
  (Matrix.trace (W.toBlocks₁₁ * K.toBlocks₂₂ᵀ + K.toBlocks₁₁ * W.toBlocks₂₂ᵀ) -
    ∑ i, ∑ j, (W.toBlocks₁₂ i j * star (K.toBlocks₁₂ j i) +
      K.toBlocks₁₂ i j * star (W.toBlocks₁₂ j i))).re

theorem symplecticP_add (W K : CotangentMatrix n) :
    symplecticP (W + K) = symplecticP W + symplecticCross W K + symplecticP K := by
  have h := symplecticP_add_expansion W K
  simp only [symplecticCross, symplecticP, Matrix.trace_add, Finset.sum_add_distrib,
    Complex.sub_re, Complex.add_re] at h ⊢
  linarith

theorem symplecticCross_add_left (W K L : CotangentMatrix n) :
    symplecticCross (W + K) L = symplecticCross W L + symplecticCross K L := by
  have h11 : (W + K).toBlocks₁₁ = W.toBlocks₁₁ + K.toBlocks₁₁ := rfl
  have h12 : (W + K).toBlocks₁₂ = W.toBlocks₁₂ + K.toBlocks₁₂ := rfl
  have h22 : (W + K).toBlocks₂₂ = W.toBlocks₂₂ + K.toBlocks₂₂ := rfl
  simp only [symplecticCross, h11, h12, h22, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.trace_add, Matrix.add_apply, star_add, add_mul, mul_add,
    Finset.sum_add_distrib, Complex.sub_re, Complex.add_re]
  ring

theorem symplecticCross_comm (W K : CotangentMatrix n) :
    symplecticCross W K = symplecticCross K W := by
  unfold symplecticCross
  rw [add_comm (W.toBlocks₁₁ * K.toBlocks₂₂ᵀ)]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact add_comm _ _

theorem symplecticCross_smul_left (c : ℝ) (W K : CotangentMatrix n) :
    symplecticCross (c • W) K = c * symplecticCross W K := by
  have h11 : (c • W).toBlocks₁₁ = c • W.toBlocks₁₁ := rfl
  have h12 : (c • W).toBlocks₁₂ = c • W.toBlocks₁₂ := rfl
  have h22 : (c • W).toBlocks₂₂ = c • W.toBlocks₂₂ := rfl
  simp only [symplecticCross, h11, h12, h22, Matrix.transpose_smul,
    Matrix.smul_mul, Matrix.mul_smul, ← smul_add, Matrix.trace_smul, Matrix.smul_apply,
    star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    ← smul_add, ← Finset.smul_sum, ← smul_sub]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem symplecticCross_smul_right (c : ℝ) (W K : CotangentMatrix n) :
    symplecticCross W (c • K) = c * symplecticCross W K := by
  rw [symplecticCross_comm W, symplecticCross_smul_left, symplecticCross_comm K]

theorem symplecticP_smul_real (c : ℝ) (W : CotangentMatrix n) :
    symplecticP (c • W) = c ^ 2 * symplecticP W := by
  have h11 : (c • W).toBlocks₁₁ = c • W.toBlocks₁₁ := rfl
  have h12 : (c • W).toBlocks₁₂ = c • W.toBlocks₁₂ := rfl
  have h22 : (c • W).toBlocks₂₂ = c • W.toBlocks₂₂ := rfl
  simp only [symplecticP, h11, h12, h22, Matrix.transpose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, Matrix.smul_apply,
    star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    smul_smul, ← Finset.smul_sum, ← smul_sub]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, pow_two]

theorem continuous_symplecticP : Continuous (symplecticP : CotangentMatrix n → ℝ) := by
  have hE (i j : CotangentIndex n) : Continuous (fun W : CotangentMatrix n => W i j) :=
    (continuous_apply j).comp (continuous_apply i)
  unfold symplecticP
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.of_apply]
  fun_prop

theorem continuous_symplecticCross :
    Continuous (fun p : CotangentMatrix n × CotangentMatrix n => symplecticCross p.1 p.2) := by
  have hE (i j : CotangentIndex n) : Continuous (fun W : CotangentMatrix n => W i j) :=
    (continuous_apply j).comp (continuous_apply i)
  unfold symplecticCross
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.of_apply]
  fun_prop

end Yau.Blueprint.V04Proof.WallErrorAux
