import Yau.Proofs.P06WeitzenbockSpectralEnergy

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Weitzenbock
open Yau G01Aux G04Aux Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

/-- A pointwise h-unitary eigenframe exists in every dimension, including
zero. No choice is made in a neighborhood and no eigenframe is differentiated. -/
theorem exists_relative_unitary_eigenframe (H A : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (hA : A.IsHermitian) :
    ∃ (E : Matrix (Fin n) (Fin n) ℂ) (eig : Fin n → ℝ),
      Eᴴ * H * E = 1 ∧ A = H * E * Matrix.diagonal (fun i => (eig i : ℂ)) * Eᴴ * H := by
  let S := CFC.sqrt H⁻¹
  have hS : S.IsHermitian := by
    simpa only [S, sub_zero] using (CFC.sqrt_nonneg H⁻¹).isHermitian
  have hSS : S * S = H⁻¹ := by
    simpa only [S, pow_two] using CFC.sq_sqrt H⁻¹ hH.posSemidef.inv.nonneg
  have hHinv : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H (hH.isUnit.map Matrix.detMonoidHom)
  have hHinv' : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H (hH.isUnit.map Matrix.detMonoidHom)
  have hHSS : H * S * S = 1 := by rw [Matrix.mul_assoc, hSS, hHinv]
  have hSHS : S * H * S = 1 := by
    have he : S * (H * S) = 1 := mul_eq_one_comm.mp hHSS
    simpa only [Matrix.mul_assoc] using he
  have hSSH : S * S * H = 1 := by rw [hSS, hHinv']
  let C := S * A * S
  have hC : C.IsHermitian := by
    change (S * A * S)ᴴ = S * A * S
    simp only [Matrix.conjTranspose_mul, hS.eq, hA.eq, Matrix.mul_assoc]
  let U : Matrix (Fin n) (Fin n) ℂ := hC.eigenvectorUnitary
  let eig := hC.eigenvalues
  have hUU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hC.eigenvectorUnitary
  have hspec : C = U * Matrix.diagonal (fun i => (eig i : ℂ)) * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, U, eig, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose] using hC.spectral_theorem
  refine ⟨S * U, eig, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, hS.eq]
    calc
      _ = Uᴴ * (S * H * S) * U := by noncomm_ring
      _ = _ := by rw [hSHS, Matrix.mul_one, hUU]
  · calc
      A = (H * S * S) * A * (S * S * H) := by rw [hHSS, hSSH]; simp
      _ = H * S * C * S * H := by dsimp [C]; noncomm_ring
      _ = H * (S * U) * Matrix.diagonal (fun i => (eig i : ℂ)) * (S * U)ᴴ * H := by
        rw [hspec, Matrix.conjTranspose_mul, hS.eq]
        noncomm_ring

variable {M : ComplexManifold n}

theorem unitary_frame_column_norm (h : HermitianField M) (x : M.Carrier)
    (E : Matrix (Fin n) (Fin n) ℂ) (hE : Eᴴ * gMat h x * E = 1) (i : Fin n) :
    hermitianNormSq (h x) (chartVec x x (matrixColumn E i)) = 1 := by
  have hm : matrixPairing (gMat h x) (matrixColumn E i) (matrixColumn E i) =
      (Eᴴ * gMat h x * E) i i := by
    simp only [matrixPairing, matrixColumn, PiLp.toLp_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hp := hMat_matrixPairing h x (chartPt x x) (matrixColumn E i) (matrixColumn E i)
  rw [hx] at hp
  change matrixPairing (gMat h x) (matrixColumn E i) (matrixColumn E i) = _ at hp
  unfold hermitianNormSq
  rw [← hp, hm, hE]
  simp

end Yau.NodeProofs.P06Weitzenbock
