import Yau.Proofs.F01NormalizeHermitian

/-! One actual invertible change of complex coordinates normalizes the
background metric and diagonalizes a second Hermitian form. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem simultaneous_hermitian_normalization (H K : Matrix ι ι ℂ)
    (hH : H.PosDef) (hK : K.IsHermitian) :
    ∃ A : Matrix ι ι ℂ, IsUnit A ∧ Aᴴ * H * A = 1 ∧
      ∃ values : ι → ℝ, Aᴴ * K * A = Matrix.diagonal (fun i => (values i : ℂ)) := by
  obtain ⟨N, hN, hNH⟩ := positive_hermitian_normalization H hH
  let G := Nᴴ * K * N
  have hG : G.IsHermitian := by
    change (Nᴴ * K * N)ᴴ = Nᴴ * K * N
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hK.eq, Matrix.mul_assoc]
  let U : Matrix ι ι ℂ := hG.eigenvectorUnitary
  have hU : IsUnit U := Unitary.isUnit_coe
  have hUU : Uᴴ * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hG.eigenvectorUnitary
  have hUG : Uᴴ * G * U = Matrix.diagonal (fun i => (hG.eigenvalues i : ℂ)) := by
    simpa only [U, Unitary.conjStarAlgAut_star_apply, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose] using
        hG.conjStarAlgAut_star_eigenvectorUnitary
  refine ⟨N * U, hN.mul hU, ?_, hG.eigenvalues, ?_⟩
  · calc
      (N * U)ᴴ * H * (N * U) = Uᴴ * (Nᴴ * H * N) * U := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hNH, Matrix.mul_one, hUU]
  · calc
      (N * U)ᴴ * K * (N * U) = Uᴴ * G * U := by
        simp only [Matrix.conjTranspose_mul, G, Matrix.mul_assoc]
      _ = _ := hUG

end Yau.NodeProofs.F01Aux
