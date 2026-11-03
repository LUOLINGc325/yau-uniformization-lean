import Yau.Geometry.Basic

/-! The actual C² positive-part cubic used by the moving compact bump. -/

noncomputable section
open Filter Asymptotics
open scoped Topology

namespace Yau.Proofs.F03Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def positivePower (k : ℕ) (r : ℝ) : ℝ := max 0 r ^ k

theorem positivePower_norm_le (k : ℕ) (r : ℝ) : ‖positivePower k r‖ ≤ ‖r ^ k‖ := by
  by_cases hr : 0 ≤ r
  · simp only [positivePower, max_eq_right hr, le_refl]
  · have h : r ≤ 0 := le_of_not_ge hr
    simp only [positivePower, max_eq_left h, norm_pow, norm_zero]
    exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0) (norm_nonneg r) k

theorem positivePower_hasDerivAt_zero (k : ℕ) (hk : 2 ≤ k) :
    HasDerivAt (positivePower k) 0 0 := by
  have hb : positivePower k =O[𝓝 (0 : ℝ)] fun r => r ^ k :=
    isBigO_of_le (𝓝 (0 : ℝ)) (positivePower_norm_le k)
  have hl : positivePower k =o[𝓝 (0 : ℝ)] fun r => r := by
    simpa only [pow_one] using hb.trans_isLittleO
      (isLittleO_pow_pow (by omega : 1 < k) (𝕜 := ℝ))
  apply HasDerivAt.of_isLittleO
  have hz : positivePower k 0 = 0 := by simp [positivePower, zero_pow (by omega : k ≠ 0)]
  simpa only [hz, sub_zero, smul_zero] using hl

theorem positivePower_hasDerivAt (k : ℕ) (hk : 2 ≤ k) (r : ℝ) :
    HasDerivAt (positivePower k) ((k : ℝ) * positivePower (k - 1) r) r := by
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · have heq : positivePower k =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_lt_nhds hr] with x hx
      simp [positivePower, max_eq_left hx.le, zero_pow (by omega : k ≠ 0)]
    have hd := (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq heq
    simpa [positivePower, max_eq_left hr.le, zero_pow (by omega : k - 1 ≠ 0)] using hd
  · simpa [positivePower, zero_pow (by omega : k - 1 ≠ 0)] using
      positivePower_hasDerivAt_zero k hk
  · have heq : positivePower k =ᶠ[𝓝 r] (fun x => x ^ k) := by
      filter_upwards [eventually_gt_nhds hr] with x hx
      simp only [positivePower, max_eq_right hx.le]
    have hd := ((hasDerivAt_id r).pow k).congr_of_eventuallyEq heq
    simpa [positivePower, max_eq_right hr.le] using hd

theorem positivePower_deriv (k : ℕ) (hk : 2 ≤ k) :
    deriv (positivePower k) = fun r => (k : ℝ) * positivePower (k - 1) r :=
  funext (fun r => (positivePower_hasDerivAt k hk r).deriv)

theorem positivePower_two_contDiff : ContDiff ℝ 1 (positivePower 2) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun r => (positivePower_hasDerivAt 2 (by omega) r).differentiableAt, ?_⟩
  rw [positivePower_deriv 2 (by omega)]
  simp only [Nat.reduceSub, positivePower, pow_one, Nat.cast_ofNat]
  exact continuous_const.mul (continuous_const.max continuous_id)

theorem positivePower_three_contDiff : ContDiff ℝ 2 (positivePower 3) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun r => (positivePower_hasDerivAt 3 (by omega) r).differentiableAt, by simp, ?_⟩
  rw [positivePower_deriv 3 (by omega)]
  exact contDiff_const.mul positivePower_two_contDiff

end Yau.Proofs.F03Aux
