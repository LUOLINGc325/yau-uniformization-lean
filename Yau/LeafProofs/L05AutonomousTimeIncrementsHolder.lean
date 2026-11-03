import Yau.LeafProofs.L05AutonomousTimeIncrements

open Set Filter MeasureTheory
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L05AutonomousAux

def autoGrowingDifference (f : ℝ → ℝ) (t h : ℝ) (k : ℕ) : ℝ :=
  (f t-f (t-(2 : ℝ)^k*h))/(2 : ℝ)^k

theorem auto_growingDifference_sub (f : ℝ → ℝ) (t h : ℝ) (k : ℕ) :
    autoGrowingDifference f t h k-autoGrowingDifference f t h (k+1)=
      autoRealSecond f t ((2 : ℝ)^k*h)/(2 : ℝ)^(k+1) := by
  unfold autoGrowingDifference autoRealSecond
  rw [pow_succ]
  have hArg : 2*((2 : ℝ)^k*h)=(2 : ℝ)^k*2*h := by ring
  rw [hArg]
  field_simp
  ring

theorem auto_growing_coefficient {h : ℝ} (hh : 0 ≤ h) (s : ℝ) (k : ℕ) :
    (((2 : ℝ)^k*h)^s)/(2 : ℝ)^(k+1)=h^s/2*((2 : ℝ)^s/2)^k := by
  rw [Real.mul_rpow (pow_nonneg (by norm_num) _) hh,← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2),
    div_pow,pow_succ]
  ring

theorem auto_finite_first_difference {a b d s A : ℝ} (_hd : 0 < d) (hA : 0 ≤ A)
    {f : ℝ → ℝ}
    (hSecond : ∀ t h : ℝ, 0 < h → a ≤ t-2*h → t ≤ b → |autoRealSecond f t h| ≤ A*h^s)
    {t h : ℝ} (ht : t∈Icc (a+d) b) (hh : 0 < h) (N : ℕ) (hN : (2 : ℝ)^N*h ≤ d)
    (hs : (2 : ℝ)^s/2 < 1) :
    |f t-f (t-h)| ≤ |autoGrowingDifference f t h N|+A*h^s/(2*(1-(2 : ℝ)^s/2)) := by
  have hStep (k : ℕ) (hk : k∈Finset.range N) :
      dist (autoGrowingDifference f t h k) (autoGrowingDifference f t h (k+1)) ≤
        A*h^s/2*((2 : ℝ)^s/2)^k := by
    have hkN : k+1 ≤ N := by have hklt := Finset.mem_range.mp hk; omega
    have hPow : (2 : ℝ)^(k+1) ≤ (2 : ℝ)^N := pow_le_pow_right₀ (by norm_num) hkN
    have hScale : 2*((2 : ℝ)^k*h) ≤ d := by rw [pow_succ] at hPow; nlinarith
    have hSec := hSecond t ((2 : ℝ)^k*h) (mul_pos (pow_pos (by norm_num) _) hh)
      (by linarith [ht.1]) ht.2
    rw [Real.dist_eq,auto_growingDifference_sub,abs_div,abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)]
    calc
      _ ≤ A*(((2 : ℝ)^k*h)^s)/(2 : ℝ)^(k+1) := div_le_div_of_nonneg_right hSec (by positivity)
      _ = _ := by rw [mul_div_assoc,auto_growing_coefficient hh.le]; ring
  have hSum := (dist_le_range_sum_dist (autoGrowingDifference f t h) N).trans
    (Finset.sum_le_sum hStep)
  have hGeom := auto_geometric_sum_bound (by positivity : (0 : ℝ) ≤ (2 : ℝ)^s/2) hs N
  rw [← Finset.mul_sum] at hSum
  have hBound := mul_le_mul_of_nonneg_left hGeom (by positivity : 0 ≤ A*h^s/2)
  have hTri : |f t-f (t-h)| ≤ dist (autoGrowingDifference f t h 0) (autoGrowingDifference f t h N)+
      |autoGrowingDifference f t h N| := by
    have h := abs_add_le (autoGrowingDifference f t h 0-autoGrowingDifference f t h N)
      (autoGrowingDifference f t h N)
    simpa only [sub_add_cancel,autoGrowingDifference,pow_zero,one_mul,div_one,Real.dist_eq] using h
  have hDen : (A*h^s/2)*(1/(1-(2 : ℝ)^s/2))=A*h^s/(2*(1-(2 : ℝ)^s/2)) := by
    field_simp
  linarith

theorem auto_second_first_holder {a b d s : ℝ} (hd : 0 < d) (_hab : a+d < b)
    (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ M A : ℝ, 0 ≤ M → 0 ≤ A → ∀ f : ℝ → ℝ,
      ContinuousOn f (Icc a b) → (∀ t∈Icc a b, |f t| ≤ M) →
      (∀ t h : ℝ, 0 < h → a ≤ t-2*h → t ≤ b → |autoRealSecond f t h| ≤ A*h^s) →
      ∀ x∈Icc (a+d) b, ∀ y∈Icc (a+d) b, |f x-f y| ≤ C*(M+A)*|x-y|^s := by
  let r := (2 : ℝ)^s/2
  have hr0 : 0 < r := div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)
  have hr1 : r < 1 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hs1
    rw [Real.rpow_one] at h
    dsimp only [r]
    linarith
  let B := 2*(2/d)^s
  let D := 1/(2*(1-r))
  let C := 1+B+D
  have hB : 0 < B := mul_pos (by norm_num) (Real.rpow_pos_of_pos (div_pos (by norm_num) hd) _)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro M A hM hA f _hCont hBound hSecond
  have hBackward {t h : ℝ} (ht : t∈Icc (a+d) b) (hh : 0 < h) (hth : t-h∈Icc (a+d) b) :
      |f t-f (t-h)| ≤ C*(M+A)*h^s := by
    have htI : t∈Icc a b := ⟨by linarith [ht.1],ht.2⟩
    have hthI : t-h∈Icc a b := ⟨by linarith [hth.1],hth.2⟩
    have hBase : |f t-f (t-h)| ≤ 2*M := (abs_sub _ _).trans (by linarith [hBound t htI,hBound (t-h) hthI])
    by_cases hSmall : h ≤ d
    · obtain ⟨N,hN0,hN1⟩ := exists_nat_pow_near ((one_le_div hh).mpr hSmall) (by norm_num : (1 : ℝ) < 2)
      have hPN : 0 < (2 : ℝ)^N := pow_pos (by norm_num) _
      have hNH : (2 : ℝ)^N*h ≤ d := (le_div_iff₀ hh).mp hN0
      have hNH' : d < 2*(2 : ℝ)^N*h := by
        have h := (div_lt_iff₀ hh).mp hN1
        rw [pow_succ] at h
        nlinarith
      have hCoarseI : t-(2 : ℝ)^N*h∈Icc a b := ⟨by linarith [ht.1],by nlinarith [ht.2]⟩
      have hCoarse : |autoGrowingDifference f t h N| ≤ 2*M/(2 : ℝ)^N := by
        rw [autoGrowingDifference,abs_div,abs_of_pos hPN]
        apply div_le_div_of_nonneg_right _ hPN.le
        exact (abs_sub _ _).trans (by linarith [hBound t htI,hBound _ hCoarseI])
      have hInv : 1/(2 : ℝ)^N ≤ (2/d)*h := by
        have hDiv := (div_le_div_iff₀ hPN hd).mpr (show 1*d ≤ (2*h)*(2 : ℝ)^N by nlinarith)
        convert hDiv using 1; ring
      have hInvPow : 1/(2 : ℝ)^N ≤ (2/d)^s*h^s := by
        have hInvOne : 1/(2 : ℝ)^N ≤ 1 := (div_le_one hPN).mpr (one_le_pow₀ (by norm_num))
        have h := Real.self_le_rpow_of_le_one (by positivity : 0 ≤ 1/(2 : ℝ)^N) hInvOne hs1.le
        have hPow := Real.rpow_le_rpow (by positivity : 0 ≤ 1/(2 : ℝ)^N) hInv hs0.le
        rw [Real.mul_rpow (div_pos (by norm_num) hd).le hh.le] at hPow
        exact h.trans hPow
      have hCoarse' : |autoGrowingDifference f t h N| ≤ B*M*h^s := hCoarse.trans (by
        have h := mul_le_mul_of_nonneg_left hInvPow (by positivity : 0 ≤ 2*M)
        dsimp only [B]
        convert h using 1 <;> ring)
      have hFinite := auto_finite_first_difference hd hA hSecond ht hh N hNH hr1
      have hCoeff : A*h^s/(2*(1-(2 : ℝ)^s/2))=D*A*h^s := by dsimp only [D,r]; ring
      rw [hCoeff] at hFinite
      dsimp only [C]
      nlinarith [Real.rpow_nonneg hh.le s,mul_nonneg hA hB.le,mul_nonneg hM hD.le]
    · have hScale : 1 ≤ (2/d)*h := by
        have hdh : d < h := lt_of_not_ge hSmall
        have h := (le_div_iff₀ hd).mpr (show 1*d ≤ 2*h by linarith)
        convert h using 1 <;> ring
      have hPow : 1 ≤ (2/d)^s*h^s := by
        have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hScale hs0.le
        rw [Real.one_rpow,Real.mul_rpow (div_pos (by norm_num) hd).le hh.le] at h
        exact h
      have hMain : 2*M ≤ B*M*h^s := by
        have h := mul_le_mul_of_nonneg_left hPow (by positivity : 0 ≤ 2*M)
        dsimp only [B]
        nlinarith
      dsimp only [C]
      have hp := Real.rpow_nonneg hh.le s
      nlinarith [mul_nonneg hA hB.le,mul_nonneg hA hD.le,mul_nonneg hM hD.le]
  intro x hx y hy
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have h := hBackward hy (sub_pos.mpr hxy) (by simpa only [sub_sub_cancel] using hx)
    rw [abs_sub_comm (f x) (f y),abs_sub_comm x y,abs_of_pos (sub_pos.mpr hxy)]
    simpa only [sub_sub_cancel] using h
  · subst y
    simp only [sub_self,abs_zero,Real.zero_rpow hs0.ne',mul_zero,le_refl]
  · have h := hBackward hx (sub_pos.mpr hxy) (by simpa only [sub_sub_cancel] using hy)
    simpa only [sub_sub_cancel,abs_of_pos (sub_pos.mpr hxy)] using h

end Yau.LeafProofs.L05AutonomousAux
