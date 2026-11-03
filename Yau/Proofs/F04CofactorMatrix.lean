import Yau.Proofs.F04Cofactor
import Yau.LeafProofs.L14

/-! The cofactor bound for the actual pair of Hermitian metric matrices. -/

open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace Yau.F04Proof

variable {n : ℕ}

theorem cofactor_trace_bound_one (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (hLE : (1 - H).PosSemidef) :
    H.det.re * traceWith H 1 ≤ n := by
  let U := hH.isHermitian.eigenvectorUnitary
  let eigen := hH.isHermitian.eigenvalues
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => (eigen i : ℂ))
  have hUD : (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * U = D := by
    have he := hH.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] at he
    convert he using 1
    ext i j
    simp [D, eigen, Function.comp_def]
  have hUU : (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * U = 1 := by
    exact Unitary.coe_star_mul_self U
  have hDiag : (1 - D).PosSemidef := by
    have hp := hLE.conjTranspose_mul_mul_same (U : Matrix (Fin n) (Fin n) ℂ)
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU, hUD] using hp
  have heigen0 (i : Fin n) : 0 < eigen i := hH.eigenvalues_pos i
  have heigen1 (i : Fin n) : eigen i ≤ 1 := by
    have hi := (Complex.nonneg_iff.mp (hDiag.diag_nonneg (i := i))).1
    simpa [D, sub_nonneg] using hi
  have heigenne (i : Fin n) : (eigen i : ℂ) ≠ 0 := by
    exact_mod_cast (heigen0 i).ne'
  have hDinv : D⁻¹ = Matrix.diagonal (fun i => (eigen i : ℂ)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    change Matrix.diagonal (fun i => (eigen i : ℂ)⁻¹) *
      Matrix.diagonal (fun i => (eigen i : ℂ)) = 1
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [heigenne]
    · simp [hij]
  have htrace : traceWith H 1 = ∑ i, (eigen i)⁻¹ := by
    have hc := congrArg Complex.re (LeafProofs.L14Aux.trace_inv_congruence H 1
      (U : Matrix (Fin n) (Fin n) ℂ)
      ((Unitary.isUnit_coe (U := U)).map Matrix.detMonoidHom))
    rw [Matrix.mul_one, hUU, hUD] at hc
    change traceWith D 1 = traceWith H 1 at hc
    rw [← hc]
    simp [traceWith, hDinv, Matrix.trace]
  have hdet : H.det.re = ∏ i, eigen i := by
    rw [hH.isHermitian.det_eq_prod_eigenvalues]
    change (∏ i, (eigen i : ℂ)).re = ∏ i, eigen i
    simp only [← Complex.ofReal_prod, Complex.ofReal_re]
  rw [htrace, hdet]
  simpa using cofactor_eigenvalue_sum_le eigen heigen0 heigen1

end Yau.F04Proof
