import Yau.Proofs.D02DiscMobius

/-! The actual opposite-parameter Möbius map is the inverse on the
closed unit disc. In particular the open disc maps bijectively to itself. -/

open scoped Topology ComplexConjugate
open Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux

theorem discMobius_inverse_numerator {a z : ℂ} (hd : 1 + conj a * z ≠ 0) :
    (-a + discMobius a z) * (1 + conj a * z) = z * (1 - conj a * a) := by
  dsimp [discMobius]
  rw [add_mul, div_mul_cancel₀ _ hd]
  ring

theorem discMobius_inverse_denominator {a z : ℂ} (hd : 1 + conj a * z ≠ 0) :
    (1 + conj (-a) * discMobius a z) * (1 + conj a * z) = 1 - conj a * a := by
  simp only [discMobius, map_neg]
  rw [add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hd]
  ring

theorem discMobius_inverse {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    discMobius (-a) (discMobius a z) = z := by
  have hna : ‖-a‖ < 1 := by simpa only [norm_neg] using ha
  have hd := discMobius_denom_ne_zero ha hz
  have hi := discMobius_denom_ne_zero hna (discMobius_norm_le_one ha hz)
  change (-a + discMobius a z) / (1 + conj (-a) * discMobius a z) = z
  apply (div_eq_iff hi).mpr
  apply mul_right_cancel₀ hd
  calc
    _ = z * (1 - conj a * a) := discMobius_inverse_numerator hd
    _ = z * ((1 + conj (-a) * discMobius a z) * (1 + conj a * z)) :=
      congrArg (fun w => z * w) (discMobius_inverse_denominator hd).symm
    _ = _ := (mul_assoc _ _ _).symm

theorem discMobius_bijOn_ball {a : ℂ} (ha : ‖a‖ < 1) :
    BijOn (discMobius a) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  refine ⟨fun z hz => ?_, ?_, ?_⟩
  · simpa only [mem_ball, dist_zero_right] using
      discMobius_norm_lt_one ha (show ‖z‖ < 1 from by simpa only [mem_ball, dist_zero_right] using hz)
  · intro z hz w hw hzw
    have hz' : ‖z‖ ≤ 1 := (show ‖z‖ < 1 from by simpa only [mem_ball, dist_zero_right] using hz).le
    have hw' : ‖w‖ ≤ 1 := (show ‖w‖ < 1 from by simpa only [mem_ball, dist_zero_right] using hw).le
    calc
      z = discMobius (-a) (discMobius a z) := (discMobius_inverse ha hz').symm
      _ = discMobius (-a) (discMobius a w) := congrArg (discMobius (-a)) hzw
      _ = w := discMobius_inverse ha hw'
  · intro w hw
    have hna : ‖-a‖ < 1 := by simpa only [norm_neg] using ha
    have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    refine ⟨discMobius (-a) w, ?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right] using discMobius_norm_lt_one hna hw'
    · simpa only [neg_neg] using discMobius_inverse hna hw'.le

end Yau.NodeProofs.D02Aux
