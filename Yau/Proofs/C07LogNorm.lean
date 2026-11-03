import Yau.Proofs.C07NormRegularization

open scoped Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Yau.Proofs.D04Aux

variable {n m : ℕ}

/-- The genuine extended logarithm, with value minus infinity at a zero. -/
def extendedLogNorm (f : ComplexVector n → ComplexVector m) (z : ComplexVector n) : EReal :=
  ENNReal.log (ENNReal.ofReal ‖f z‖)

theorem extendedLogNorm_le_real_iff (f : ComplexVector n → ComplexVector m)
    (z : ComplexVector n) (b : ℝ) :
    extendedLogNorm f z ≤ (b : EReal) ↔ ‖f z‖ ≤ Real.exp b := by
  have he : ENNReal.log (ENNReal.ofReal (Real.exp b)) = (b : EReal) := by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos b), Real.log_exp]
  rw [extendedLogNorm, ← he, ENNReal.log_le_log_iff,
    ENNReal.ofReal_le_ofReal_iff (Real.exp_pos b).le]

/-- Holomorphic vector maps have psh extended logarithmic norm on their full
open domain. Zeros are handled by actual nonvanishing holomorphic
augmentations and the original continuous-majorant submean predicate. -/
theorem extendedLogNorm_isPshOn {Ω : Set (ComplexVector n)} (hΩ : IsOpen Ω)
    {f : ComplexVector n → ComplexVector m} (hf : DifferentiableOn ℂ f Ω) :
    IsPshOn (extendedLogNorm f) Ω := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    simp only [extendedLogNorm, ENNReal.log_lt_top_iff, ENNReal.ofReal_lt_top]
  · exact (ENNReal.continuous_log.comp_continuousOn
      (ENNReal.continuous_ofReal.comp_continuousOn hf.continuousOn.norm)).upperSemicontinuousOn
  · intro z w hdisc φ hφ hmajor
    by_cases hzero : f z = 0
    · simp [extendedLogNorm, hzero]
    have hzn : 0 < ‖f z‖ := norm_pos_iff.mpr hzero
    rw [extendedLogNorm, ENNReal.log_ofReal_of_pos hzn]
    apply EReal.coe_le_coe_iff.mpr
    apply le_of_forall_pos_le_add
    intro η hη
    obtain ⟨M, hM⟩ := isCompact_Icc.bddBelow_image hφ.continuousOn
    have heη : 0 < Real.exp η - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hη)
    let ε := (Real.exp η - 1) * Real.exp M / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hpsh := augmentNorm_log_isPshOn hΩ hf hε
    have hmean := intervalMajorant_submean hpsh z w hdisc
      (hφ.add continuous_const) (by
        intro θ hθ
        let y := z + Complex.exp (θ * Complex.I) • w
        have hMy : M ≤ φ θ := hM (Set.mem_image_of_mem φ hθ)
        have hnorm : ‖f y‖ ≤ Real.exp (φ θ) :=
          (extendedLogNorm_le_real_iff f y (φ θ)).mp (hmajor θ)
        have hεbound : ε ≤ (Real.exp η - 1) * Real.exp (φ θ) := by
          have hmexp := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hMy) heη.le
          dsimp [ε]
          nlinarith [mul_pos heη (Real.exp_pos M)]
        have haug : ‖augmentNorm f ε y‖ ≤ Real.exp (φ θ + η) := by
          have hb := (augmentNorm_bounds f hε.le y).2
          rw [Real.exp_add]
          nlinarith
        have haugn : 0 < ‖augmentNorm f ε y‖ := by
          have hs := augmentNorm_sq f ε y
          nlinarith [norm_nonneg (augmentNorm f ε y), sq_nonneg ‖f y‖]
        exact EReal.coe_le_coe_iff.mpr ((Real.log_le_iff_le_exp haugn).mpr haug))
    change (Real.log ‖augmentNorm f ε z‖ : EReal) ≤
      (circleAverage (fun θ => φ θ + η) : EReal) at hmean
    rw [circleAverage_add_const hφ η] at hmean
    have hmeanReal : Real.log ‖augmentNorm f ε z‖ ≤ circleAverage φ + η :=
      EReal.coe_le_coe_iff.mp hmean
    exact (Real.log_le_log hzn (augmentNorm_bounds f hε.le z).1).trans hmeanReal

end Yau.Proofs.C07Aux
