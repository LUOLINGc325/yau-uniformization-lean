import Yau.Proofs.C01CotangentJetAlgebra

/-! Taking a positive metric trace preserves nonnegativity of the real
quadratic curvature values.  The trace argument needs no extra hypothesis
that a separately supplied curvature tensor is Hermitian. -/

noncomputable section

open scoped Matrix ComplexOrder MatrixOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem trace_congruence_eq_column_quadratics (B A : Herm n) (hB : B.IsHermitian) :
    Matrix.trace (B * A * B) =
      ∑ i, star (fun j => B j i) ⬝ᵥ (A *ᵥ (fun j => B j i)) := by
  have hstar (i j : Fin n) : star (B j i) = B i j :=
    congrArg (fun C : Herm n => C i j) hB.eq
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, hstar, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem trace_mul_nonneg_of_real_quadratics (H A : Herm n) (hH : H.PosSemidef)
    (hA : ∀ v : Fin n → ℂ, 0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re) :
    0 ≤ (Matrix.trace (H * A)).re := by
  let B := CFC.sqrt H
  have hB : B.IsHermitian :=
    ((Matrix.nonneg_iff_posSemidef).mp (CFC.sqrt_nonneg H)).1
  have hsq : B * B = H := CFC.sqrt_mul_sqrt_self H hH.nonneg
  have htrace : Matrix.trace (H * A) = Matrix.trace (B * A * B) := by
    rw [Matrix.trace_mul_cycle, hsq, Matrix.trace_mul_comm]
  rw [htrace, trace_congruence_eq_column_quadratics B A hB]
  have hsum := Complex.re_sum Finset.univ
    (fun i => star (fun j => B j i) ⬝ᵥ (A *ᵥ (fun j => B j i)))
  exact hsum.symm ▸ Finset.sum_nonneg (fun i _ => hA (fun j => B j i))

end Yau.NodeProofs.C01Aux
