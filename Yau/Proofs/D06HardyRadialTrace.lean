import Yau.Proofs.D06HardyTraceMap

/-! The radial L² trace is the actual holomorphic evaluation on the smaller
circle. All traces belong to the same Fourier construction. -/

open scoped lp
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardy_fourier_nat (n : ℕ) (t : HardyCircle) :
    fourier (n : ℤ) t = (fourier 1 t) ^ n := by
  induction n with
  | zero => simpa only [Nat.cast_zero, pow_zero] using (fourier_zero (x := t))
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

theorem hardyRadial_pad_summable_norm (s : ℂ) (hs : ‖s‖ < 1) (a : HardySeq r) (j : Fin r) :
    Summable (fun n : ℤ => ‖hardyPad (hardyDilate s hs.le a) j n‖) := by
  apply Summable.of_nat_of_neg_add_one
  · simp only [hardyPad_nat, hardyDilate_apply, norm_mul, norm_pow]
    apply ((summable_geometric_of_lt_one (norm_nonneg s) hs).mul_right ‖a‖).of_nonneg_of_le
      (fun _ => mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))
    intro n
    exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (p := 2) (by norm_num) a (n, j))
      (pow_nonneg (norm_nonneg _) _)
  · simp only [hardyPad_negSucc, norm_zero]
    exact summable_zero

theorem hardyTraceLp_radial_ae (s : ℂ) (hs : ‖s‖ < 1) (a : HardySeq r) (j : Fin r) :
    (fun t => hardyTraceLp (hardyDilate s hs.le a) j t) =ᵐ[hardyCircleMeasure]
      (fun t => hardyEvalEntry a j (s * fourier 1 t)) := by
  let b := hardyDilate s hs.le a
  let f : ℤ → Lp ℂ 2 hardyCircleMeasure := fun n => hardyPad b j n • fourierLp 2 n
  have hsum : HasSum f (hardyTraceLp b j) := by
    simpa only [f, hardyTrace_fourierCoeff, hardyPad_apply] using
      hasSum_fourier_series_L2 (hardyTraceLp b j)
  have hn : Summable (fun n : ℤ => ‖f n‖) := by
    have hb : ∀ n : ℤ, ‖fourierLp (T := 2 * Real.pi) 2 n‖ = 1 :=
      orthonormal_fourier.norm_eq_one
    simp only [f, norm_smul, hb, mul_one]
    exact hardyRadial_pad_summable_norm s hs a j
  have hterms (n : ℤ) : (fun t => f n t) =ᵐ[hardyCircleMeasure]
      fun t => hardyPad b j n * fourier n t := by
    filter_upwards [Lp.coeFn_smul (hardyPad b j n) (fourierLp 2 n),
      coeFn_fourierLp (T := 2 * Real.pi) 2 n] with t h1 h2
    exact h1.trans (by rw [Pi.smul_apply, smul_eq_mul, h2])
  have ht : ∀ᵐ t ∂hardyCircleMeasure, ∀ n : ℤ, f n t = hardyPad b j n * fourier n t :=
    ae_all_iff.mpr hterms
  have hc := Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hn)
  rw [hsum.tsum_eq] at hc
  filter_upwards [hc, ht] with t hct htt
  apply hct.trans
  rw [hardyEvalEntry_eq_tsum]
  have hp : Summable (fun n : ℕ => hardyPad b j n * fourier (n : ℤ) t) := by
    apply Summable.of_norm
    have h := (hardyRadial_pad_summable_norm s hs a j).comp_injective Int.ofNat_injective
    apply h.congr
    intro n
    change ‖hardyPad b j (n : ℤ)‖ = ‖hardyPad b j (n : ℤ) * fourier (n : ℤ) t‖
    rw [norm_mul]
    simp only [fourier_apply, Circle.norm_coe, mul_one]
  have hm : Summable (fun n : ℕ => hardyPad b j (-(n + 1)) * fourier (-(n + 1)) t) := by
    simp only [hardyPad_negSucc, zero_mul]
    exact summable_zero
  have hsplit := tsum_of_nat_of_neg_add_one
    (f := fun n : ℤ => hardyPad b j n * fourier n t) hp hm
  calc
    (∑' n : ℤ, f n t) = ∑' n : ℤ, hardyPad b j n * fourier n t := tsum_congr htt
    _ = ∑' n : ℕ, hardyPad b j n * fourier (n : ℤ) t := by
      simpa only [hardyPad_negSucc, zero_mul, tsum_zero, add_zero] using hsplit
    _ = _ := by
      apply tsum_congr
      intro n
      rw [hardyPad_nat, hardyDilate_apply, hardy_fourier_nat, mul_pow]
      ring

end Yau.NodeProofs.D06Aux
