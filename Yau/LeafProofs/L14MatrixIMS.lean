import Yau.LeafProofs.L14Symbols

noncomputable section
open scoped ComplexOrder Matrix
namespace Yau.LeafProofs.L14Aux

def matrixHermitianMetric {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (hM : M.PosDef) : Yau.HermitianInnerProduct (ι → ℂ) where
  toFun u v := star u ⬝ᵥ M *ᵥ v
  map_add_left u v w := by
    simp only [dotProduct, Pi.star_apply, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]
  map_smul_left c u v := by
    simp only [dotProduct, Pi.star_apply, Pi.smul_apply, star_mul, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  map_add_right u v w := by rw [Matrix.mulVec_add, dotProduct_add]
  map_smul_right c u v := by rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_comm]
  conjugate_symmetric u v := (hM.isHermitian.star_dotProduct_mulVec_comm v u).symm
  self_adjoint u := (Complex.nonneg_iff.mp (hM.posSemidef.dotProduct_mulVec_nonneg u)).2.symm
  positive_definite u := by
    refine ⟨(Complex.nonneg_iff.mp (hM.posSemidef.dotProduct_mulVec_nonneg u)).1, ?_⟩
    constructor
    · intro hz
      by_contra hu
      have hp := (Complex.pos_iff.mp (hM.dotProduct_mulVec_pos hu)).1
      linarith
    · intro hu
      subst u
      simp only [Matrix.mulVec_zero, dotProduct_zero, Complex.zero_re]

theorem finite_matrix_IMS {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix κ κ ℂ) (hM : M.PosDef) (χ : ι → ℝ) (v : κ → ℂ) (w : ι → κ → ℂ)
    (hχ : ∑ i, χ i ^ 2 = 1) (hw : ∑ i, (χ i : ℂ) • w i = 0) :
    (∑ i, (star ((χ i : ℂ) • v + w i) ⬝ᵥ M *ᵥ ((χ i : ℂ) • v + w i)).re) =
      (star v ⬝ᵥ M *ᵥ v).re + ∑ i, (star (w i) ⬝ᵥ M *ᵥ w i).re :=
  finite_hermitian_IMS (matrixHermitianMetric M hM) χ v w hχ hw

end Yau.LeafProofs.L14Aux
