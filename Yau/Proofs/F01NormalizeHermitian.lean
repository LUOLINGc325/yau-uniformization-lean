import spec.CHAIN.CONTRACTS

/-! Actual invertible complex normalization of a positive Hermitian matrix.
No positive-dimension premise is required. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positive_hermitian_normalization (H : Matrix ι ι ℂ) (hH : H.PosDef) :
    ∃ A : Matrix ι ι ℂ, IsUnit A ∧ Aᴴ * H * A = 1 := by
  let U : Matrix ι ι ℂ := hH.isHermitian.eigenvectorUnitary
  let D : Matrix ι ι ℂ := Matrix.diagonal
    (fun i => (((Real.sqrt (hH.isHermitian.eigenvalues i))⁻¹ : ℝ) : ℂ))
  have hU : Uᴴ * H * U = Matrix.diagonal
      (fun i => (hH.isHermitian.eigenvalues i : ℂ)) := by
    simpa only [U, Unitary.conjStarAlgAut_star_apply, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose] using hH.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hscalar (i : ι) : ((Real.sqrt (hH.isHermitian.eigenvalues i) : ℝ) : ℂ)⁻¹ *
      (hH.isHermitian.eigenvalues i : ℂ) *
        ((Real.sqrt (hH.isHermitian.eigenvalues i) : ℝ) : ℂ)⁻¹ = 1 := by
    have hp := hH.eigenvalues_pos i
    have hs := Real.sqrt_pos.mpr hp
    have hv : (Real.sqrt (hH.isHermitian.eigenvalues i))⁻¹ *
        hH.isHermitian.eigenvalues i * (Real.sqrt (hH.isHermitian.eigenvalues i))⁻¹ = 1 := by
      field_simp [hs.ne']
      nlinarith [Real.sq_sqrt hp.le]
    exact_mod_cast hv
  have hD : Dᴴ * Matrix.diagonal (fun i => (hH.isHermitian.eigenvalues i : ℂ)) * D = 1 := by
    dsimp [D]
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      have hs : star (((Real.sqrt (hH.isHermitian.eigenvalues i))⁻¹ : ℝ) : ℂ) =
          (((Real.sqrt (hH.isHermitian.eigenvalues i))⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Function.comp_apply,
        Pi.star_apply]
      rw [hs]
      simpa only [Complex.ofReal_inv] using hscalar i
    · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hA : (U * D)ᴴ * H * (U * D) = 1 := by
    calc
      (U * D)ᴴ * H * (U * D) = Dᴴ * (Uᴴ * H * U) * D := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hU]; exact hD
  refine ⟨U * D, ?_, hA⟩
  apply (Matrix.isUnit_iff_isUnit_det (U * D)).mpr
  exact Matrix.isUnit_det_of_left_inverse hA

end Yau.NodeProofs.F01Aux
