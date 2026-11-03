import Yau.LeafProofs.L16ResidualEstimates

/-! Uniform value convergence and a common original Hölder bound imply
convergence in half the exponent. This supplies the genuine Banach graph
limit used at a positive maximal time, without higher derivative budgets. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E]

theorem F05_holderWeight_half_square (α : ℝ) (p q : Point n) :
    holderWeight α p q ≤ (holderWeight (α/2) p q)^2 := by
  have hX : (‖p.1-q.1‖^(α/2))^2 = ‖p.1-q.1‖^α := by
    rw [← Real.rpow_two,← Real.rpow_mul (norm_nonneg _),show α/2*2 = α by ring]
  have hT : (|p.2-q.2|^((α/2)/2))^2 = |p.2-q.2|^(α/2) := by
    rw [← Real.rpow_two,← Real.rpow_mul (abs_nonneg _),show (α/2)/2*2 = α/2 by ring]
  have hCross := mul_nonneg (Real.rpow_nonneg (norm_nonneg (p.1-q.1)) (α/2))
    (Real.rpow_nonneg (abs_nonneg (p.2-q.2)) ((α/2)/2))
  dsimp only [holderWeight]
  nlinarith

theorem F05_holder_half_interpolation {α C ε : ℝ} {Q : Set (Point n)} {f : Point n → E}
    (hε : 0 ≤ ε) (hf : HolderBound α Q f C) (hSup : ∀ p ∈ Q, ‖f p‖ ≤ ε) :
    HolderBound (α/2) Q f (ε+Real.sqrt (2*ε*C)) := by
  have hC : 0 ≤ C := hf.1
  have hRad : 0 ≤ 2*ε*C := by positivity
  refine ⟨by positivity,?_,?_⟩
  · intro p hp
    exact (hSup p hp).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · intro p hp q hq
    let W := holderWeight (α/2) p q
    have hW : 0 ≤ W := by dsimp only [W,holderWeight]; positivity
    have hLow : ‖f p-f q‖ ≤ 2*ε :=
      (norm_sub_le _ _).trans (by linarith [hSup p hp,hSup q hq])
    have hHigh : ‖f p-f q‖ ≤ C*W^2 := (hf.2.2 p hp q hq).trans
      (mul_le_mul_of_nonneg_left (F05_holderWeight_half_square α p q) hC)
    have hSquare : ‖f p-f q‖^2 ≤ (2*ε*C)*W^2 := by
      have hProd := mul_le_mul hLow hHigh (norm_nonneg _) (by positivity : 0 ≤ 2*ε)
      nlinarith
    have hBoundSq : ‖f p-f q‖^2 ≤ (Real.sqrt (2*ε*C)*W)^2 := by
      rw [mul_pow,Real.sq_sqrt hRad]
      exact hSquare
    have hBound := (sq_le_sq₀ (norm_nonneg (f p-f q)) (mul_nonneg (Real.sqrt_nonneg _) hW)).mp hBoundSq
    exact hBound.trans (mul_le_mul_of_nonneg_right (by linarith : Real.sqrt (2*ε*C) ≤ ε+Real.sqrt (2*ε*C)) hW)

end Yau.Proofs.F05Aux
