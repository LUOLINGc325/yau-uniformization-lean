import Yau.Blueprint.Nodes
import Mathlib.Analysis.Matrix.PosDef

/-! Complete the scalar Harnack square with the paper covector convention.
The inverse transpose in `dualNormMat` is retained throughout. -/

open scoped BigOperators ComplexOrder

noncomputable section

namespace Yau.Proofs.C05Aux

open Yau Matrix

variable {n : ℕ}

theorem dualNormMat_eq_linear_inverse (A : Matrix (Fin n) (Fin n) ℂ)
    (p : ComplexVector n) :
    dualNormMat A p =
      (WithLp.ofLp p ⬝ᵥ (A⁻¹ *ᵥ star (WithLp.ofLp p))).re := by
  unfold dualNormMat
  rw [dotProduct_transpose_mulVec]

theorem scalar_harnack_minimum (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (p : ComplexVector n) (S : ℝ)
    (hH : ∀ v : Fin n → ℂ,
      0 ≤ S + 2 * (∑ i, v i * p i).re + (star v ⬝ᵥ (A *ᵥ v)).re) :
    0 ≤ dualNormMat A p ∧ dualNormMat A p ≤ S := by
  let q : Fin n → ℂ := A⁻¹ *ᵥ star (WithLp.ofLp p)
  have hq : A *ᵥ q = star (WithLp.ofLp p) := by
    dsimp [q]
    rw [mulVec_mulVec, mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (hA.posSemidef.posDef_iff_det_ne_zero.mp hA)), one_mulVec]
  have he : (star q ⬝ᵥ (A *ᵥ q)).re = dualNormMat A p := by
    rw [hq, dualNormMat_eq_linear_inverse]
    change (star q ⬝ᵥ star (WithLp.ofLp p)).re = (WithLp.ofLp p ⬝ᵥ q).re
    rw [star_dotProduct_star]
    simp only [Complex.star_def, Complex.conj_re]
  refine ⟨?_, ?_⟩
  · rw [← he]
    exact (Complex.nonneg_iff.mp (hA.posSemidef.dotProduct_mulVec_nonneg q)).1
  · have hh := hH (-q)
    have hl : (∑ i, (-q) i * p i).re = -dualNormMat A p := by
      rw [dualNormMat_eq_linear_inverse]
      change (∑ i, -q i * p i).re = -(WithLp.ofLp p ⬝ᵥ q).re
      simp only [neg_mul, Finset.sum_neg_distrib, Complex.neg_re]
      congr 1
      simp only [dotProduct, mul_comm]
    have hneg : (star (-q) ⬝ᵥ (A *ᵥ (-q))).re = dualNormMat A p := by
      simpa only [mulVec_neg, star_neg, neg_dotProduct, dotProduct_neg, neg_neg] using he
    rw [hl, hneg] at hh
    linarith

end Yau.Proofs.C05Aux
