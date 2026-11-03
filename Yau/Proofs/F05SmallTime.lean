import Mathlib

/-! The parametrix time and interpolation scale are selected uniformly before
the current endpoint and every source function. -/

noncomputable section

namespace Yau.Proofs.F05Aux

theorem F05_uniform_small_time {α E δ₀ : ℝ} (hα : α < 1) (hE : 0 < E) (hδ₀ : 0 < δ₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ δ ≤ 1 ∧
      ∀ T : ℝ, 0 < T → T ≤ δ → E * T ^ ((1-α)/2) ≤ 1/4 := by
  let θ := (1-α)/2
  have hθ : 0 < θ := by dsimp only [θ]; linarith
  let b := 1/(4*E)
  have hb : 0 < b := by dsimp only [b]; positivity
  let S := b ^ (1/θ)
  have hS : 0 < S := Real.rpow_pos_of_pos hb _
  let δ := min δ₀ (min 1 S)
  have hδ : 0 < δ := lt_min hδ₀ (lt_min zero_lt_one hS)
  refine ⟨δ,hδ,min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),?_⟩
  intro T hT hTδ
  have hTS : T ≤ S := hTδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hPower : S ^ θ = b := by
    dsimp only [S]
    rw [← Real.rpow_mul hb.le,div_mul_cancel₀ 1 hθ.ne',Real.rpow_one]
  have hBound : T ^ θ ≤ b := (Real.rpow_le_rpow hT.le hTS hθ.le).trans_eq hPower
  change E * T ^ θ ≤ 1/4
  calc
    E * T ^ θ ≤ E*b := mul_le_mul_of_nonneg_left hBound hE.le
    _ = 1/4 := by dsimp only [b]; field_simp

theorem F05_sqrt_scale {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (α : ℝ) :
    0 < Real.sqrt T ∧ Real.sqrt T ≤ 1 ∧ T = (Real.sqrt T)^2 ∧
      (Real.sqrt T) ^ (1-α) = T ^ ((1-α)/2) := by
  refine ⟨Real.sqrt_pos.mpr hT,Real.sqrt_le_one.mpr hT1,(Real.sq_sqrt hT.le).symm,?_⟩
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul hT.le]
  congr 1
  ring

end Yau.Proofs.F05Aux
