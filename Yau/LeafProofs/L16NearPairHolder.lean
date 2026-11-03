import Yau.LeafProofs.L16InteriorPlateauJets

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- Uniform control on nearby space-time pairs and a supremum bound give
    a full Holder bound, without any covering or prior seminorm finiteness. -/
theorem holderBound_of_near_pairs {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C0 C1 εx εt : ℝ} {Q : Set (Point n)} {f : Point n → V}
    (hα : 0 ≤ α) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hεx : 0 < εx) (hεt : 0 < εt)
    (hSup : ∀ p ∈ Q, ‖f p‖ ≤ C0)
    (hNear : ∀ p ∈ Q, ∀ q ∈ Q, ‖p.1-q.1‖ ≤ εx → |p.2-q.2| ≤ εt →
      ‖f p-f q‖ ≤ C1*holderWeight α p q) :
    HolderBound α Q f (C0+C1+2*C0*εx^(-α)+2*C0*εt^(-α/2)) := by
  let C : ℝ := C0+C1+2*C0*εx^(-α)+2*C0*εt^(-α/2)
  have hX : 0 ≤ 2*C0*εx^(-α) := by positivity
  have hTime : 0 ≤ 2*C0*εt^(-α/2) := by positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hC0C : C0 ≤ C := by dsimp only [C]; linarith
  have hC1C : C1 ≤ C := by dsimp only [C]; linarith
  have hXC : 2*C0*εx^(-α) ≤ C := by dsimp only [C]; linarith
  have hTC : 2*C0*εt^(-α/2) ≤ C := by dsimp only [C]; linarith
  refine ⟨hC,fun p hp => (hSup p hp).trans hC0C,?_⟩
  intro p hp q hq
  have hW : 0 ≤ holderWeight α p q := by dsimp only [holderWeight]; positivity
  have hDiff : ‖f p-f q‖ ≤ 2*C0 := by
    calc
      _ ≤ ‖f p‖+‖f q‖ := norm_sub_le _ _
      _ ≤ C0+C0 := add_le_add (hSup p hp) (hSup q hq)
      _ = _ := by ring
  have hFar (s x e : ℝ) (hs : 0 < s) (he : 0 ≤ e) (hsx : s ≤ x)
      (hxW : x^e ≤ holderWeight α p q) :
      ‖f p-f q‖ ≤ (2*C0*s^(-e))*holderWeight α p q := by
    have hPow : s^e ≤ x^e := Real.rpow_le_rpow hs.le hsx he
    have hOne : 1 ≤ s^(-e)*holderWeight α p q := by
      calc
        1 = s^(-e)*s^e := by rw [← Real.rpow_add hs,neg_add_cancel,Real.rpow_zero]
        _ ≤ s^(-e)*x^e := mul_le_mul_of_nonneg_left hPow (Real.rpow_nonneg hs.le _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hxW (Real.rpow_nonneg hs.le _)
    calc
      _ ≤ 2*C0 := hDiff
      _ ≤ 2*C0*(s^(-e)*holderWeight α p q) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hOne (by positivity : 0 ≤ 2*C0)
      _ = _ := by ring
  by_cases hSpace : ‖p.1-q.1‖ ≤ εx
  · by_cases hTemporal : |p.2-q.2| ≤ εt
    · exact (hNear p hp q hq hSpace hTemporal).trans
        (mul_le_mul_of_nonneg_right hC1C hW)
    · have hFarTime := hFar εt |p.2-q.2| (α/2) hεt (by positivity)
        (le_of_not_ge hTemporal)
        (le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _))
      have hCoeff : 2*C0*εt^(-(α/2)) ≤ C := by
        convert hTC using 1
        congr 1
        ring
      exact hFarTime.trans (mul_le_mul_of_nonneg_right hCoeff hW)
  · exact (hFar εx ‖p.1-q.1‖ α hεx hα (le_of_not_ge hSpace)
      (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _))).trans
        (mul_le_mul_of_nonneg_right hXC hW)

end Yau.LeafProofs.L16Aux
