import Yau.Proofs.Y03QuadraticForm

/-! Small generic quadratic-form API, independent of the C04 flow estimates. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.Proofs.C04Aux
open Yau Blueprint Matrix

variable {n : ℕ}

theorem matrixForm_add (A B : Herm n) (v : Fin n → ℂ) :
    Blueprint.Alignment.Y03Proof.matrixForm (A + B) v =
      Blueprint.Alignment.Y03Proof.matrixForm A v + Blueprint.Alignment.Y03Proof.matrixForm B v := by
  simp only [Blueprint.Alignment.Y03Proof.matrixForm, Matrix.add_mulVec, dotProduct_add, Complex.add_re]

theorem matrixForm_real_smul (c : ℝ) (A : Herm n) (v : Fin n → ℂ) :
    Blueprint.Alignment.Y03Proof.matrixForm ((c : ℂ) • A) v = c * Blueprint.Alignment.Y03Proof.matrixForm A v := by
  simp only [Blueprint.Alignment.Y03Proof.matrixForm, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem matrixForm_order {A B : Herm n} (hAB : HermLE A B) (v : Fin n → ℂ) :
    Blueprint.Alignment.Y03Proof.matrixForm A v ≤ Blueprint.Alignment.Y03Proof.matrixForm B v := by
  have hh := hAB.re_dotProduct_nonneg v
  change 0 ≤ (star v ⬝ᵥ ((B - A) *ᵥ v)).re at hh
  simpa only [Blueprint.Alignment.Y03Proof.matrixForm, Matrix.sub_mulVec, dotProduct_sub,
    Complex.sub_re, sub_nonneg] using hh

theorem HermLE_of_matrixForm_le {H G : Herm n} (hH : H.IsHermitian) (hG : G.IsHermitian)
    (hform : ∀ v, Blueprint.Alignment.Y03Proof.matrixForm H v ≤
      Blueprint.Alignment.Y03Proof.matrixForm G v) : HermLE H G := by
  have hsub : (G - H).IsHermitian := hG.sub hH
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsub
  intro v
  apply Complex.nonneg_iff.mpr
  constructor
  · have hh := hform v
    simpa only [Blueprint.Alignment.Y03Proof.matrixForm, Matrix.sub_mulVec,
      dotProduct_sub, Complex.sub_re, sub_nonneg] using hh
  · have hh := congrArg Complex.im (hsub.star_dotProduct_mulVec_comm v v)
    change -(star v ⬝ᵥ ((G - H) *ᵥ v)).im = (star v ⬝ᵥ ((G - H) *ᵥ v)).im at hh
    linarith

theorem matrixForm_neg (H : Herm n) (v : Fin n → ℂ) :
    Blueprint.Alignment.Y03Proof.matrixForm (-H) v = -Blueprint.Alignment.Y03Proof.matrixForm H v := by
  simp only [Blueprint.Alignment.Y03Proof.matrixForm, Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]

end Yau.Proofs.C04Aux
