import Yau.LeafProofs.L05AutonomousTimeIncrementsDerivativeHolder

open Set Filter MeasureTheory Metric
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L05AutonomousAux

def autoSlopeErrorFactor (s : ℝ) : ℝ := 1/(1-(1/2 : ℝ)^(s-1))

theorem auto_slopeErrorFactor_pos {s : ℝ} (hs : 1 < s) : 0 < autoSlopeErrorFactor s := by
  have h := Real.rpow_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1) (by linarith : 0 < s-1)
  exact one_div_pos.mpr (sub_pos.mpr h)

theorem auto_second_derivative {a b d s : ℝ} (hd : 0 < d) (hab : a+d < b)
    (hs : 1 < s) (_hs2 : s < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ M A : ℝ, 0 ≤ M → 0 ≤ A → ∀ f : ℝ → ℝ,
      ContinuousOn f (Icc a b) → (∀ t∈Icc a b, |f t| ≤ M) →
      (∀ t h : ℝ, 0 < h → a ≤ t-2*h → t ≤ b → |autoRealSecond f t h| ≤ A*h^s) →
      ∃ V : ℝ → ℝ, ContinuousOn V (Icc (a+d) b) ∧
        (∀ t∈Icc (a+d) b, |V t| ≤ C*(M+A)) ∧
        (∀ x∈Icc (a+d) b, ∀ y∈Icc (a+d) b, |V x-V y| ≤ C*A*|x-y|^(s-1)) ∧
        (∀ t∈Icc (a+d) b, ∀ h : ℝ, 0 < h → h ≤ d/2 →
          |(f t-f (t-h))/h-V t| ≤ C*A*h^(s-1)) ∧
        (∀ x∈Icc (a+d) b, ∀ y∈Icc (a+d) b, f y-f x=∫ t in x..y, V t) ∧
        (∀ t∈Ioo (a+d) b, HasDerivAt f (V t) t) ∧
        (∀ t∈Icc (a+d) b, HasDerivWithinAt f (V t) (Icc (a+d) b) t) := by
  let E := autoSlopeErrorFactor s
  let S := 2/(d/2)+E*(d/2)^(s-1)
  let H := autoDerivativeHolderFactor a b d E
  let C := 1+E+S+H
  have hE : 0 < E := auto_slopeErrorFactor_pos hs
  have hS : 0 < S := add_pos (div_pos (by norm_num) (half_pos hd))
    (mul_pos hE (Real.rpow_pos_of_pos (half_pos hd) _))
  have hH : 0 < H := auto_derivativeHolderFactor_pos a b d hE.le
  have hC : 0 < C := by dsimp only [C]; linarith
  have hEC : E ≤ C := by dsimp only [C]; linarith
  have hSC : S ≤ C := by dsimp only [C]; linarith
  have hHC : H ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro M A hM hA f hf hBound hSecond
  obtain ⟨V,hV,hError,hFTC,hAt,hWithin⟩ := auto_second_derivative_core hd hab hA hs hf hSecond
  have hErr : ∀ t∈Icc (a+d) b, ∀ h : ℝ, 0 < h → h ≤ d/2 →
      |autoBackwardSlope f t h-V t| ≤ E*A*h^(s-1) := hError
  have hHolder := auto_derivative_holder_of_slope_error hd hab hA hE.le hs hSecond hErr
  refine ⟨V,hV,?_,?_,?_,hFTC,hAt,hWithin⟩
  · intro t ht
    have htI : t∈Icc a b := ⟨by linarith [ht.1],ht.2⟩
    have hthI : t-d/2∈Icc a b := ⟨by linarith [ht.1],by linarith [ht.2]⟩
    have hSlope : |autoBackwardSlope f t (d/2)| ≤ 2*M/(d/2) := by
      rw [autoBackwardSlope,abs_div,abs_of_pos (half_pos hd)]
      apply div_le_div_of_nonneg_right _ (half_pos hd).le
      exact (abs_sub _ _).trans (by linarith [hBound t htI,hBound _ hthI])
    have hErr0 := hErr t ht (d/2) (half_pos hd) le_rfl
    have hTri : |V t| ≤ |autoBackwardSlope f t (d/2)-V t|+|autoBackwardSlope f t (d/2)| := by
      have h := abs_add_le (-(autoBackwardSlope f t (d/2)-V t)) (autoBackwardSlope f t (d/2))
      simpa only [neg_sub,sub_add_cancel,abs_neg,abs_sub_comm (V t) (autoBackwardSlope f t (d/2))] using h
    have hSM : |V t| ≤ S*(M+A) := by
      have hMain : |V t| ≤ E*(d/2)^(s-1)*A+(2/(d/2))*M := by
        have h := hTri.trans (add_le_add hErr0 hSlope)
        convert h using 1; ring
      have hNonneg1 := mul_nonneg (mul_pos hE (Real.rpow_pos_of_pos (half_pos hd) (s-1))).le hM
      have hNonneg2 := mul_nonneg (div_pos (by norm_num : (0 : ℝ) < 2) (half_pos hd)).le hA
      dsimp only [S]
      nlinarith
    exact hSM.trans (mul_le_mul_of_nonneg_right hSC (add_nonneg hM hA))
  · intro x hx y hy
    have h := hHolder x hx y hy
    have hInc := mul_le_mul_of_nonneg_right hHC (mul_nonneg hA (Real.rpow_nonneg (abs_nonneg (x-y)) (s-1)))
    exact h.trans (by convert hInc using 1 <;> ring)
  · intro t ht h hh hhd
    have h := hErr t ht h hh hhd
    have hInc := mul_le_mul_of_nonneg_right hEC (mul_nonneg hA (Real.rpow_nonneg hh.le (s-1)))
    exact h.trans (by convert hInc using 1 <;> ring)

end Yau.LeafProofs.L05AutonomousAux
