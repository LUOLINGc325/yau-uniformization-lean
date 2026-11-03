import Yau.Proofs.V03MatrixKahlerTwoForm

/-! The actual Hermitian two-form is invariant under the complex
structure, and its complex diagonal is exactly the original area density. -/

open scoped Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {ι : Type*} [Fintype ι] {H : Matrix ι ι ℂ}

theorem matrixKahlerTwoForm_J (hH : H.IsHermitian) (u v : EuclideanSpace ℂ ι) :
    matrixKahlerTwoForm H ![Complex.I • u, Complex.I • v] = matrixKahlerTwoForm H ![u, v] := by
  rw [matrixKahlerTwoForm_apply hH, matrixKahlerTwoForm_apply hH]
  have hfun (w : EuclideanSpace ℂ ι) : (fun i => (Complex.I • w) i) = Complex.I • (fun i => w i) := by
    funext i
    rfl
  rw [hfun u, hfun v, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_I]
  congr 2
  calc
    _ = -(Complex.I * Complex.I) * (star (fun i => u i) ⬝ᵥ (H *ᵥ fun i => v i)) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem matrixKahlerTwoForm_diagonal (hH : H.IsHermitian) (u : EuclideanSpace ℂ ι) :
    matrixKahlerTwoForm H ![u, Complex.I • u] =
      2 * (star (fun i => u i) ⬝ᵥ (H *ᵥ fun i => u i)).re := by
  rw [matrixKahlerTwoForm_apply hH]
  have hfun : (fun i => (Complex.I • u) i) = Complex.I • (fun i => u i) := by
    funext i
    rfl
  rw [hfun, Matrix.mulVec_smul, dotProduct_smul]
  simp only [smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]

end Yau.Blueprint.V03Proof
