import Yau.Proofs.C04MatrixRegularity

/-! The genuine nonnegative variance in the matrix Harnack log-convexity calculation. -/

noncomputable section
open scoped ComplexOrder Matrix

namespace Yau.Proofs.C04Aux
open Yau Blueprint
open Matrix
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def realMatrixPairing (H : Herm n) (v w : Fin n → ℂ) : ℝ :=
  (star v ⬝ᵥ (H *ᵥ w)).re

theorem realMatrixPairing_cauchy (H : Herm n) (hH : H.PosDef) (v w : Fin n → ℂ) :
    (realMatrixPairing H v w) ^ 2 ≤ realMatrixPairing H v v * realMatrixPairing H w w := by
  letI : SeminormedAddCommGroup (Fin n → ℂ) := H.toSeminormedAddCommGroup hH.posSemidef
  letI : InnerProductSpace ℂ (Fin n → ℂ) := H.toInnerProductSpace hH.posSemidef
  have hrepr (v w : Fin n → ℂ) : realMatrixPairing H v w = (inner ℂ v w).re := by
    change (star v ⬝ᵥ (H *ᵥ w)).re = ((H *ᵥ w) ⬝ᵥ star v).re
    rw [dotProduct_comm]
  have hc := inner_mul_inner_self_le (𝕜 := ℂ) v w
  rw [← norm_inner_symm v w] at hc
  have hsq := (sq_le_sq₀ (abs_nonneg (inner ℂ v w).re)
    (norm_nonneg (inner ℂ v w))).mpr (Complex.abs_re_le_norm (inner ℂ v w))
  rw [sq_abs] at hsq
  have hh := hsq.trans (by simpa only [pow_two] using hc)
  change (inner ℂ v w).re ^ 2 ≤ (inner ℂ v v).re * (inner ℂ w w).re at hh
  simpa only [← hrepr] using hh

theorem realMatrixPairing_conjugate (H A B : Herm n) (v w : Fin n → ℂ) :
    realMatrixPairing H (A *ᵥ v) (B *ᵥ w) = realMatrixPairing (A.conjTranspose * H * B) v w := by
  simp only [realMatrixPairing, star_mulVec, dotProduct_mulVec, vecMul_vecMul,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem inverse_ricci_variance (K R : Herm n) (hK : K.PosDef) (hR : R.IsHermitian)
    (v : Fin n → ℂ) :
    (Blueprint.Alignment.Y03Proof.matrixForm (K * R * K) v) ^ 2 ≤
      Blueprint.Alignment.Y03Proof.matrixForm K v *
        Blueprint.Alignment.Y03Proof.matrixForm (K * R * K * R * K) v := by
  have hh := realMatrixPairing_cauchy K hK v ((R * K) *ᵥ v)
  have hcross : realMatrixPairing K v ((R * K) *ᵥ v) =
      Blueprint.Alignment.Y03Proof.matrixForm (K * R * K) v := by
    simp only [realMatrixPairing, Blueprint.Alignment.Y03Proof.matrixForm,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hlast : realMatrixPairing K ((R * K) *ᵥ v) ((R * K) *ᵥ v) =
      Blueprint.Alignment.Y03Proof.matrixForm (K * R * K * R * K) v := by
    rw [realMatrixPairing_conjugate]
    simp only [Matrix.conjTranspose_mul, hK.isHermitian.eq, hR.eq,
      Matrix.mul_assoc, realMatrixPairing, Blueprint.Alignment.Y03Proof.matrixForm]
  rw [hcross, hlast] at hh
  exact hh

end Yau.Proofs.C04Aux
