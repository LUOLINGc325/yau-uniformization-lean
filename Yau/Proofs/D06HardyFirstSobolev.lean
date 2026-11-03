import Yau.Proofs.D06HardyDifferenceParseval
import Yau.Proofs.D06FourierSlope

/-! Finite Fourier differences give one full angular L² derivative of the
same original Hardy coefficient sequence, without changing its witness. -/

open scoped lp Topology
open Filter MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardy_first_moment_of_difference_bound (a : HardySeq r) (C : ℝ)
    (hbound : ∀ θ : ℝ, ‖hardyDilate (fourier 1 (θ : HardyCircle))
      (by simp only [fourier_apply, Circle.norm_coe, le_refl]) a - a‖ ^ 2 ≤ C * θ ^ 2) :
    Summable (fun k : ℕ × Fin r => (k.1 : ℝ) ^ 2 * ‖a k‖ ^ 2) := by
  apply summable_of_sum_le (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  intro F
  have hfinite (l : ℕ) : (∑ k ∈ F, ‖hardyFourierQuotient k.1 l‖ ^ 2 * ‖a k‖ ^ 2) ≤ C := by
    let θ := hardySmallAngle l
    let R := hardyDilate (fourier 1 (θ : HardyCircle))
      (by simp only [fourier_apply, Circle.norm_coe, le_refl]) a - a
    have hR : (∑ k ∈ F, ‖R k‖ ^ 2) ≤ ‖R‖ ^ 2 := by
      have hn : (∑' k : ℕ × Fin r, ‖R k‖ ^ 2) = ‖R‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (lp.hasSum_norm (p := 2) (by norm_num) R).tsum_eq
      exact ((hardy_summable_norm_sq R).sum_le_tsum F (fun _ _ => sq_nonneg _)).trans_eq hn
    have hθ : θ ≠ 0 := (hardySmallAngle_pos l).ne'
    have hb : (θ⁻¹) ^ 2 * (∑ k ∈ F, ‖R k‖ ^ 2) ≤ C := by
      have h := mul_le_mul_of_nonneg_left (hR.trans (hbound θ)) (sq_nonneg θ⁻¹)
      have hc : (θ⁻¹) ^ 2 * (C * θ ^ 2) = C := by field_simp
      exact h.trans_eq hc
    have heq : (∑ k ∈ F, ‖hardyFourierQuotient k.1 l‖ ^ 2 * ‖a k‖ ^ 2) =
        (θ⁻¹) ^ 2 * (∑ k ∈ F, ‖R k‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hr : R k = (fourier (k.1 : ℤ) (θ : HardyCircle) - 1) * a k := by
        change fourier 1 (θ : HardyCircle) ^ k.1 * a k - a k = _
        rw [hardy_fourier_nat]
        ring
      rw [hr, norm_mul, mul_pow]
      change ‖(θ⁻¹) • (fourier (k.1 : ℤ) (θ : HardyCircle) - 1)‖ ^ 2 * ‖a k‖ ^ 2 = _
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    exact heq.trans_le hb
  have hlim : Tendsto (fun l => ∑ k ∈ F, ‖hardyFourierQuotient k.1 l‖ ^ 2 * ‖a k‖ ^ 2)
      atTop (𝓝 (∑ k ∈ F, (k.1 : ℝ) ^ 2 * ‖a k‖ ^ 2)) :=
    tendsto_finsetSum F (fun k _ => (hardyFourierQuotient_norm_sq_tendsto k.1).mul_const _)
  exact le_of_tendsto hlim (Eventually.of_forall hfinite)

theorem hardy_column_difference_bound
    (a : Fin r → HardySeq r) (C : ℝ)
    (hbound : ∀ θ : ℝ, circleDifference (hardyMatrixTrace a) (θ : HardyCircle) ≤ C * θ ^ 2)
    (j : Fin r) (θ : ℝ) :
    ‖hardyDilate (fourier 1 (θ : HardyCircle))
      (by simp only [fourier_apply, Circle.norm_coe, le_refl]) (a j) - a j‖ ^ 2 ≤ C * θ ^ 2 := by
  have hp := hardyMatrixTrace_difference_parseval a (θ : HardyCircle)
  have hs : ‖hardyDilate (fourier 1 (θ : HardyCircle))
      (by simp only [fourier_apply, Circle.norm_coe, le_refl]) (a j) - a j‖ ^ 2 ≤
      ∑ k : Fin r, ‖hardyDilate (fourier 1 (θ : HardyCircle))
        (by simp only [fourier_apply, Circle.norm_coe, le_refl]) (a k) - a k‖ ^ 2 :=
    Finset.single_le_sum (f := fun k : Fin r => ‖hardyDilate (fourier 1 (θ : HardyCircle))
      (by simp only [fourier_apply, Circle.norm_coe, le_refl]) (a k) - a k‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  exact (hs.trans_eq hp.symm).trans (hbound θ)

end Yau.NodeProofs.D06Aux
