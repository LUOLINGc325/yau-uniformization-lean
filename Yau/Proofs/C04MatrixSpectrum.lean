import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-! The finite-dimensional determinant comparison used in metric decay. -/

noncomputable section
open scoped ComplexOrder Matrix

namespace Yau.Proofs.C04Aux

variable {n : ℕ}

theorem spectral_lower_bound {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (c : ℝ) (hc : ∀ i, c ≤ hA.eigenvalues i) :
    (A - (c : ℂ) • 1).PosSemidef := by
  let U := hA.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hAD : (U : Matrix (Fin n) (Fin n) ℂ) * D * (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose = A := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, Function.comp_def, U, D] using hA.spectral_theorem.symm
  have hD : (D - (c : ℂ) • 1).PosSemidef := by
    have heq : D - (c : ℂ) • 1 = Matrix.diagonal (fun i => ((hA.eigenvalues i - c : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j <;> simp [D, Matrix.diagonal, hij]
    rw [heq]
    exact Matrix.PosSemidef.diagonal (fun i =>
      Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr (hc i), by simp⟩)
  have hh := hD.conjTranspose_mul_mul_same (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose
  simp only [Matrix.conjTranspose_conjTranspose] at hh
  have hu : (U : Matrix (Fin n) (Fin n) ℂ) * (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 1 :=
    Unitary.coe_mul_star_self U
  have heq : (U : Matrix (Fin n) (Fin n) ℂ) * (D - (c : ℂ) • 1) *
      (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose = A - (c : ℂ) • 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hAD, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hu]
  rwa [heq] at hh

theorem eigenvalues_le_one_of_le_one {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hIA : (1 - A).PosSemidef) :
    ∀ i, hA.eigenvalues i ≤ 1 := by
  let U := hA.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hdiag : (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose * A * (U : Matrix (Fin n) (Fin n) ℂ) = D := by
    simpa only [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, Function.comp_def, U, D] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have hu : (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose * (U : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  have hh := hIA.conjTranspose_mul_mul_same (U : Matrix (Fin n) (Fin n) ℂ)
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hdiag, hu] at hh
  intro i
  have hd := (Complex.nonneg_iff.mp (hh.diag_nonneg (i := i))).1
  simpa only [D, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
    Complex.sub_re, Complex.one_re, Complex.ofReal_re, sub_nonneg] using hd

theorem determinant_lower_bound {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hIA : (1 - A).PosSemidef) :
    (A - (A.det.re : ℂ) • 1).PosSemidef := by
  have heig0 := hA.eigenvalues_pos
  have heig1 := eigenvalues_le_one_of_le_one hA.isHermitian hIA
  have hdet : A.det.re = ∏ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_prod, Complex.ofReal_re]
  apply spectral_lower_bound hA.isHermitian
  intro i
  rw [hdet]
  have hp : ∏ j ∈ Finset.univ.erase i, hA.isHermitian.eigenvalues j ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => (heig0 j).le) (fun j _ => heig1 j)
  calc
    ∏ j, hA.isHermitian.eigenvalues j =
        (∏ j ∈ Finset.univ.erase i, hA.isHermitian.eigenvalues j) * hA.isHermitian.eigenvalues i :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
    _ ≤ 1 * hA.isHermitian.eigenvalues i := mul_le_mul_of_nonneg_right hp (heig0 i).le
    _ = hA.isHermitian.eigenvalues i := one_mul _

end Yau.Proofs.C04Aux
