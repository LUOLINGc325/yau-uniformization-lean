import Yau.Proofs.C04RayleighSpectrum

/-! Concrete least/greatest Rayleigh values and the determinant product bound. -/

noncomputable section
open scoped ComplexOrder Matrix

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ}

theorem eigenvalues_ge_of_matrix_lower {A : Herm n} (hA : A.IsHermitian) (c : ℝ)
    (hc : (A - (c : ℂ) • 1).PosSemidef) : ∀ i, c ≤ hA.eigenvalues i := by
  intro i
  have hh := hc.re_dotProduct_nonneg (WithLp.ofLp (hA.eigenvectorBasis i))
  change 0 ≤ matrixQuadratic (A - (c : ℂ) • 1) (hA.eigenvectorBasis i) at hh
  rw [matrixQuadratic_sub, matrixQuadratic_real_smul, matrixQuadratic_one,
    hA.eigenvectorBasis.orthonormal.1 i] at hh
  have he : matrixQuadratic A (hA.eigenvectorBasis i) = hA.eigenvalues i := (hA.eigenvalues_eq i).symm
  rw [he] at hh
  nlinarith

theorem min_max_determinant_bounds {A : Herm n} (hn : 0 < n) (hA : A.PosDef)
    (hAI : (A - 1).PosSemidef) :
    1 ≤ relMinEigenvalue 1 A ∧ 0 < relMaxEigenvalue 1 A ∧
      (A - ((relMinEigenvalue 1 A : ℝ) : ℂ) • 1).PosSemidef ∧
      A.det.re ≤ (relMaxEigenvalue 1 A) ^ n := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨imin, hminmem, hmin⟩ := Finset.exists_min_image Finset.univ hA.isHermitian.eigenvalues Finset.univ_nonempty
  obtain ⟨imax, hmaxmem, hmax⟩ := Finset.exists_max_image Finset.univ hA.isHermitian.eigenvalues Finset.univ_nonempty
  have hminall : ∀ j, hA.isHermitian.eigenvalues imin ≤ hA.isHermitian.eigenvalues j :=
    fun j => hmin j (Finset.mem_univ j)
  have hmaxall : ∀ j, hA.isHermitian.eigenvalues j ≤ hA.isHermitian.eigenvalues imax :=
    fun j => hmax j (Finset.mem_univ j)
  have hminEq := relMin_eq_of_minimal_eigenvalue hA.isHermitian imin hminall
  have hmaxEq := relMax_eq_of_maximal_eigenvalue hA.isHermitian imax hmaxall
  have heig1 := eigenvalues_ge_of_matrix_lower hA.isHermitian 1
    (by simpa only [Complex.ofReal_one, one_smul] using hAI)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hminEq]
    exact heig1 imin
  · rw [hmaxEq]
    exact hA.eigenvalues_pos imax
  · rw [hminEq]
    exact spectral_lower_bound hA.isHermitian _ hminall
  · have hdet : A.det.re = ∏ i, hA.isHermitian.eigenvalues i := by
      rw [hA.isHermitian.det_eq_prod_eigenvalues]
      simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_prod, Complex.ofReal_re]
    rw [hdet, hmaxEq]
    calc
      ∏ i, hA.isHermitian.eigenvalues i ≤ ∏ _i : Fin n, hA.isHermitian.eigenvalues imax :=
        Finset.prod_le_prod₀ (fun i _ => (hA.eigenvalues_pos i).le) (fun i _ => hmaxall i)
      _ = (hA.isHermitian.eigenvalues imax) ^ n := by simp

end Yau.Proofs.C04Aux
