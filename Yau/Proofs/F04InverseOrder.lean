import Yau.Proofs.F04ChartEllipticity

open scoped Matrix

noncomputable section

namespace Yau.F04Proof

/-- Inversion reverses positive definite quadratic form order. The zero
 dimensional case is included without a nonempty-index premise. -/
theorem real_inverse_quadratic_order {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : (B - A).PosSemidef) (v : ι → ℝ) :
    dotProduct v (B⁻¹ *ᵥ v) ≤ dotProduct v (A⁻¹ *ᵥ v) := by
  let w := A⁻¹ *ᵥ v
  let z := B⁻¹ *ᵥ v
  have hAw : A *ᵥ w = v := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit), Matrix.one_mulVec]
  have hBz : B *ᵥ z = v := by
    dsimp only [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit), Matrix.one_mulVec]
  have hp : 0 ≤ dotProduct v w := by
    simpa only [star_trivial] using hA.inv.posSemidef.dotProduct_mulVec_nonneg v
  have hq : 0 ≤ dotProduct v z := by
    simpa only [star_trivial] using hB.inv.posSemidef.dotProduct_mulVec_nonneg v
  have hm : dotProduct z (A *ᵥ z) ≤ dotProduct v z := by
    have hn := hAB.dotProduct_mulVec_nonneg z
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hBz] at hn
    rw [dotProduct_comm z v] at hn
    linarith
  have hc := hA.star_dotProduct_mulVec_mul_le z w
  simp only [star_trivial, hAw] at hc
  rw [dotProduct_comm z v, dotProduct_comm w v] at hc
  have hmp := mul_le_mul_of_nonneg_right hm hp
  change dotProduct v z ≤ dotProduct v w
  rcases eq_or_lt_of_le hq with hz | hz
  · rw [← hz]
    exact hp
  · nlinarith

end Yau.F04Proof
