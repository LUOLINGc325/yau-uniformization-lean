import Mathlib.Analysis.Matrix.PosDef

/-! The actual positive Harnack error matrix is bounded by its scalar trace. -/

open scoped ComplexOrder
open Unitary

noncomputable section

namespace Yau.Proofs.C05Aux

variable {n : ℕ}

theorem positive_eigenvalue_le_trace (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : M.PosSemidef) (i : Fin n) : hM.isHermitian.eigenvalues i ≤ M.trace.re := by
  have ht : M.trace.re = ∑ j, hM.isHermitian.eigenvalues j := by
    rw [hM.isHermitian.trace_eq_sum_eigenvalues]
    simp
  rw [ht]
  exact Finset.single_le_sum (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ i)

set_option backward.isDefEq.respectTransparency false in
theorem positive_matrix_le_trace (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.PosSemidef) :
    (((M.trace.re : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) - M).PosSemidef := by
  let U := hM.isHermitian.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (hM.isHermitian.eigenvalues i : ℂ))
  have hD : (((M.trace.re : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) - D).PosSemidef := by
    have heq : ((M.trace.re : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) - D =
        Matrix.diagonal (fun i => ((M.trace.re - hM.isHermitian.eigenvalues i : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [D]
      · simp [D, Matrix.diagonal, hij]
    rw [heq]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact Complex.nonneg_iff.mpr ⟨by simpa using sub_nonneg.mpr (positive_eigenvalue_le_trace M hM i), by simp⟩
  have hc :
      (conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) U
        (((M.trace.re : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) - D)).PosSemidef := by
    rw [conjStarAlgAut_apply]
    exact hD.mul_mul_conjTranspose_same (U : Matrix (Fin n) (Fin n) ℂ)
  have hspec : conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) U D = M :=
    hM.isHermitian.spectral_theorem.symm
  simpa only [map_sub, map_smul, map_one, hspec] using hc

end Yau.Proofs.C05Aux
