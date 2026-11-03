import Yau.LeafProofs.L14
import Yau.Proofs.P03StrictPshCharts

open scoped Matrix Kronecker ComplexOrder

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

theorem nakanoQuadratic_add (R S : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (U : Fin n → Fin r → ℂ) :
    nakanoQuadratic (fun i j => R i j + S i j) U =
      nakanoQuadratic R U + nakanoQuadratic S U := by
  simp only [nakanoQuadratic, Matrix.add_apply, add_mul, Finset.sum_add_distrib, Complex.add_re]

/-- The derivative-index transpose in the actual weighted curvature is
exactly the Hermitian Kronecker quadratic, with no reversal of its sign. -/
theorem nakano_leviCorrection_eq_kronecker (L : Matrix (Fin n) (Fin n) ℂ)
    (H : Matrix (Fin r) (Fin r) ℂ) (U : Fin n → Fin r → ℂ) :
    nakanoQuadratic (fun i j => L j i • H) U =
      (star (fun p : Fin n × Fin r => U p.1 p.2) ⬝ᵥ
        ((L ⊗ₖ H) *ᵥ (fun p : Fin n × Fin r => U p.1 p.2))).re := by
  simp only [nakanoQuadratic, Matrix.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec,
    Fintype.sum_prod_type, Pi.star_apply, Matrix.kronecker_apply, Finset.mul_sum]
  apply congrArg Complex.re
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro β _
  ring

theorem nakano_leviCorrection_nonnegative {L : Matrix (Fin n) (Fin n) ℂ}
    {H : Matrix (Fin r) (Fin r) ℂ} (hL : L.PosSemidef) (hH : H.PosSemidef)
    (U : Fin n → Fin r → ℂ) : 0 ≤ nakanoQuadratic (fun i j => L j i • H) U := by
  rw [nakano_leviCorrection_eq_kronecker]
  exact (Complex.nonneg_iff.mp ((hL.kronecker hH).dotProduct_mulVec_nonneg _)).1

end Yau.NodeProofs.P03Aux
