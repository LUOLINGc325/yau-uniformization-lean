import Yau.Proofs.F04SourcePositive

open scoped Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem dotProduct_vecMulVec {ι : Type*} [Fintype ι] (x a b v : ι → ℂ) :
    x ⬝ᵥ (Matrix.vecMulVec a b *ᵥ v) = (x ⬝ᵥ a) * (b ⬝ᵥ v) := by
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem positive_matrix_rankOne_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ) (hG : G.PosDef) (u : ι → ℂ) :
    ((((star u ⬝ᵥ (G *ᵥ u)).re : ℂ) • G) -
      Matrix.vecMulVec (G *ᵥ u) (star (G *ᵥ u))).PosSemidef := by
  have hq := hG.posSemidef.dotProduct_mulVec_nonneg u
  have hqre : 0 ≤ (star u ⬝ᵥ (G *ᵥ u)).re := (Complex.nonneg_iff.mp hq).1
  have hqeq : (((star u ⬝ᵥ (G *ᵥ u)).re : ℝ) : ℂ) = star u ⬝ᵥ (G *ᵥ u) := by
    apply Complex.ext
    · rfl
    · change 0 = (star u ⬝ᵥ (G *ᵥ u)).im
      exact (Complex.nonneg_iff.mp hq).2
  have hscaled : ((((star u ⬝ᵥ (G *ᵥ u)).re : ℂ) • G)).PosSemidef :=
    hG.posSemidef.smul (show (0 : ℂ) ≤ ((star u ⬝ᵥ (G *ᵥ u)).re : ℂ) from
      Complex.nonneg_iff.mpr ⟨hqre, rfl⟩)
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hscaled.isHermitian.sub (Matrix.posSemidef_vecMulVec_self_star (G *ᵥ u)).isHermitian, ?_⟩
  intro v
  have h1 : star v ⬝ᵥ (G *ᵥ u) = star (star u ⬝ᵥ (G *ᵥ v)) :=
    (hG.isHermitian.star_dotProduct_mulVec_comm u v).symm
  have h2 : star (G *ᵥ u) ⬝ᵥ v = star u ⬝ᵥ (G *ᵥ v) := by
    rw [Matrix.star_dotProduct, h1, star_star]
  have houter : star v ⬝ᵥ (Matrix.vecMulVec (G *ᵥ u) (star (G *ᵥ u)) *ᵥ v) =
      star (star u ⬝ᵥ (G *ᵥ v)) * (star u ⬝ᵥ (G *ᵥ v)) := by
    calc
      _ = (star v ⬝ᵥ (G *ᵥ u)) * (star (G *ᵥ u) ⬝ᵥ v) :=
        dotProduct_vecMulVec (star v) (G *ᵥ u) (star (G *ᵥ u)) v
      _ = _ := by rw [h1, h2]
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    hqeq, houter]
  exact sub_nonneg.mpr (hG.star_dotProduct_mulVec_mul_le u v)

end Yau.F04Proof
