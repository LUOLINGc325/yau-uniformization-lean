import Yau.LeafProofs.L05AutonomousTimeIncrementsDerivativeCore

open Set Filter MeasureTheory Metric
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L05AutonomousAux

theorem auto_adjacent_slope_difference (f : ℝ → ℝ) (t h : ℝ) :
    autoBackwardSlope f t h-autoBackwardSlope f (t-h) h=autoRealSecond f t h/h := by
  unfold autoBackwardSlope autoRealSecond
  rw [show (t-h)-h=t-2*h by ring]
  ring

theorem auto_small_derivative_holder {a b d s A E : ℝ} (_hd : 0 < d) (_hA : 0 ≤ A) (hs : 1 < s)
    {f V : ℝ → ℝ}
    (hSecond : ∀ t h : ℝ, 0 < h → a ≤ t-2*h → t ≤ b → |autoRealSecond f t h| ≤ A*h^s)
    (hError : ∀ t∈Icc (a+d) b, ∀ h : ℝ, 0 < h → h ≤ d/2 →
      |autoBackwardSlope f t h-V t| ≤ E*A*h^(s-1)) :
    ∀ x∈Icc (a+d) b, ∀ y∈Icc (a+d) b, |x-y| ≤ d/2 →
      |V x-V y| ≤ (2*E+1)*A*|x-y|^(s-1) := by
  have hOrdered {x y : ℝ} (hx : x∈Icc (a+d) b) (hy : y∈Icc (a+d) b)
      (hxy : x < y) (hSmall : y-x ≤ d/2) :
      |V y-V x| ≤ (2*E+1)*A*(y-x)^(s-1) := by
    let h := y-x
    have hh : 0 < h := sub_pos.mpr hxy
    have hYX : y-h=x := by dsimp only [h]; ring
    have hEX := hError x hx h hh hSmall
    have hEY := hError y hy h hh hSmall
    have hSec := hSecond y h hh (by linarith [hy.1]) hy.2
    have hDiff : |autoBackwardSlope f y h-autoBackwardSlope f x h| ≤ A*h^(s-1) := by
      have hId := auto_adjacent_slope_difference f y h
      rw [hYX] at hId
      rw [hId,abs_div,abs_of_pos hh,Real.rpow_sub_one hh.ne']
      simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hSec hh.le
    have hTri : |V y-V x| ≤ |autoBackwardSlope f y h-V y|+
        |autoBackwardSlope f y h-autoBackwardSlope f x h|+|autoBackwardSlope f x h-V x| := by
      calc
        _ = |-(autoBackwardSlope f y h-V y)+(autoBackwardSlope f y h-autoBackwardSlope f x h)+
            (autoBackwardSlope f x h-V x)| := by congr 1; ring
        _ ≤ |-(autoBackwardSlope f y h-V y)+(autoBackwardSlope f y h-autoBackwardSlope f x h)|+
            |autoBackwardSlope f x h-V x| := abs_add_le _ _
        _ ≤ _ := by
          have hAbs := abs_add_le (-(autoBackwardSlope f y h-V y)) (autoBackwardSlope f y h-autoBackwardSlope f x h)
          simp only [abs_neg] at hAbs
          linarith only [hAbs]
    calc
      _ ≤ E*A*h^(s-1)+A*h^(s-1)+E*A*h^(s-1) :=
        hTri.trans (add_le_add (add_le_add hEY hDiff) hEX)
      _ = _ := by ring
  intro x hx y hy hSmall
  rcases lt_trichotomy x y with hxy|hxy|hxy
  · rw [abs_sub_comm (V x) (V y),abs_sub_comm x y,abs_of_pos (sub_pos.mpr hxy)]
    exact hOrdered hx hy hxy (by simpa only [abs_sub_comm x y,abs_of_pos (sub_pos.mpr hxy)] using hSmall)
  · subst y
    simp only [sub_self,abs_zero,Real.zero_rpow (by linarith : s-1 ≠ 0),mul_zero,le_refl]
  · rw [abs_of_pos (sub_pos.mpr hxy)] at hSmall ⊢
    simpa only [abs_sub_comm (V y) (V x)] using hOrdered hy hx hxy hSmall

def autoDerivativePartitionCount (a b d : ℝ) : ℕ := Nat.ceil (2*(b-a)/d)+1

def autoDerivativeHolderFactor (a b d E : ℝ) : ℝ := (autoDerivativePartitionCount a b d : ℝ)*(2*E+1)

theorem auto_derivativeHolderFactor_pos (a b d : ℝ) {E : ℝ} (hE : 0 ≤ E) :
    0 < autoDerivativeHolderFactor a b d E := by
  have hN : (0 : ℝ) < autoDerivativePartitionCount a b d := by
    unfold autoDerivativePartitionCount
    positivity
  exact mul_pos hN (by linarith)

theorem auto_derivative_holder_of_slope_error {a b d s A E : ℝ} (hd : 0 < d) (_hab : a+d < b)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hs : 1 < s) {f V : ℝ → ℝ}
    (hSecond : ∀ t h : ℝ, 0 < h → a ≤ t-2*h → t ≤ b → |autoRealSecond f t h| ≤ A*h^s)
    (hError : ∀ t∈Icc (a+d) b, ∀ h : ℝ, 0 < h → h ≤ d/2 →
      |autoBackwardSlope f t h-V t| ≤ E*A*h^(s-1)) :
    ∀ x∈Icc (a+d) b, ∀ y∈Icc (a+d) b,
      |V x-V y| ≤ autoDerivativeHolderFactor a b d E*A*|x-y|^(s-1) := by
  intro x hx y hy
  let N := autoDerivativePartitionCount a b d
  have hN : 0 < N := by dsimp only [N,autoDerivativePartitionCount]; omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNBound : 2*(b-a)/d ≤ (N : ℝ) := by
    have h := Nat.le_ceil (2*(b-a)/d)
    dsimp only [N,autoDerivativePartitionCount]
    push_cast
    linarith
  have hLength : |x-y| ≤ b-a := abs_le.mpr ⟨by linarith [hx.1,hy.2],by linarith [hy.1,hx.2]⟩
  have hStepSmall : |x-y|/(N : ℝ) ≤ d/2 := (div_le_iff₀ hNr).mpr (by
    have h := (div_le_iff₀ hd).mp hNBound
    nlinarith)
  let z : ℕ → ℝ := fun j => AffineMap.lineMap x y ((j : ℝ)/(N : ℝ))
  have hz (j : ℕ) (hj : j ≤ N) : z j∈Icc (a+d) b := by
    apply (convex_Icc (a+d) b).lineMap_mem hx hy
    exact ⟨div_nonneg (Nat.cast_nonneg _) hNr.le,(div_le_one hNr).mpr (by exact_mod_cast hj)⟩
  have hz0 : z 0=x := by simp [z]
  have hzN : z N=y := by simp [z,hNr.ne']
  have hDiff (j : ℕ) : |z j-z (j+1)|=|x-y|/(N : ℝ) := by
    have hId : z j-z (j+1)=(x-y)/(N : ℝ) := by
      dsimp only [z]
      simp only [AffineMap.lineMap_apply_module',smul_eq_mul,Nat.cast_add,Nat.cast_one]
      field_simp
      ring
    rw [hId,abs_div,abs_of_pos hNr]
  have hSmall := auto_small_derivative_holder hd hA hs hSecond hError
  have hEach (j : ℕ) (hj : j∈Finset.range N) :
      dist (V (z j)) (V (z (j+1))) ≤ (2*E+1)*A*|x-y|^(s-1) := by
    have hjN : j+1 ≤ N := by have hjlt := Finset.mem_range.mp hj; omega
    have hLocal := hSmall (z j) (hz j (by omega)) (z (j+1)) (hz (j+1) hjN) (by rw [hDiff]; exact hStepSmall)
    have hPower := Real.rpow_le_rpow (abs_nonneg (z j-z (j+1)))
      (show |z j-z (j+1)| ≤ |x-y| by rw [hDiff]; exact div_le_self (abs_nonneg _) hNr1) (by linarith : 0 ≤ s-1)
    simpa only [Real.dist_eq] using hLocal.trans (mul_le_mul_of_nonneg_left hPower (by positivity))
  have hSum := (dist_le_range_sum_dist (fun j => V (z j)) N).trans (Finset.sum_le_sum hEach)
  rw [hz0,hzN] at hSum
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Real.dist_eq] at hSum
  change _ ≤ (N : ℝ)*(2*E+1)*A*|x-y|^(s-1)
  convert hSum using 1; ring

end Yau.LeafProofs.L05AutonomousAux
