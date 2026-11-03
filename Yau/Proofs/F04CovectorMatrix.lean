import Yau.Proofs.F04RankOne

open scoped Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem covector_rankOne_bound {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ)
    (hG : G.PosDef) (c : Fin n → ℂ) :
    HermLE (Matrix.vecMulVec (star c) c)
      ((dualNormMat G (WithLp.toLp 2 c) : ℂ) • G) := by
  let u : Fin n → ℂ := G⁻¹ *ᵥ star c
  have hGu : G *ᵥ u = star c := by
    dsimp only [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hG.isUnit.map Matrix.detMonoidHom),
      Matrix.one_mulVec]
  have hquad : star u ⬝ᵥ (G *ᵥ u) = star c ⬝ᵥ ((G⁻¹)ᵀ *ᵥ c) := by
    rw [hGu]
    change star (G⁻¹ *ᵥ star c) ⬝ᵥ star c = star c ⬝ᵥ ((G⁻¹)ᵀ *ᵥ c)
    rw [Matrix.star_mulVec, star_star, hG.isHermitian.inv.eq, Matrix.mulVec_transpose,
      dotProduct_comm]
  have hqre : (star u ⬝ᵥ (G *ᵥ u)).re = dualNormMat G (WithLp.toLp 2 c) := by
    exact congrArg Complex.re hquad
  have hh := positive_matrix_rankOne_bound G hG u
  rw [hqre, hGu, star_star] at hh
  exact hh

end Yau.F04Proof
