import Yau.Proofs.C07CauchyFirst

open scoped ContDiff

namespace Yau.Proofs.C07Aux

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Constants from repeated half-ball Cauchy estimates. -/
def cauchyFactor : ℕ → ℝ
  | 0 => 1
  | m + 1 => 4 * 2 ^ m * cauchyFactor m

theorem cauchyFactor_pos (m : ℕ) : 0 < cauchyFactor m := by
  induction m with
  | zero => norm_num [cauchyFactor]
  | succ m hm => simp only [cauchyFactor]; positivity

/-- Every complex Fréchet derivative has a quantitative bound from the
same bound on the original map.  The statement includes order zero. -/
theorem iterated_cauchy_bound {f : E → G} {R B : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℂ ∞ f (Metric.ball 0 R))
    (hbound : ∀ z ∈ Metric.ball (0 : E) R, ‖f z‖ ≤ B)
    (m : ℕ) :
    ∀ z ∈ Metric.ball (0 : E) (R / 2 ^ m),
      ‖iteratedFDeriv ℂ m f z‖ ≤ cauchyFactor m * B / R ^ m := by
  induction m with
  | zero => simpa only [pow_zero, div_one, cauchyFactor, one_mul, norm_iteratedFDeriv_zero]
      using hbound
  | succ m hm =>
    have hdiff : DifferentiableOn ℂ (iteratedFDeriv ℂ m f) (Metric.ball 0 R) := by
      apply (hf.differentiableOn_iteratedFDerivWithin (m := m)
        (by exact WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top m))
        Metric.isOpen_ball.uniqueDiffOn).congr
      intro z hz
      exact (iteratedFDerivWithin_of_isOpen m Metric.isOpen_ball hz).symm
    have hrad : R / 2 ^ m ≤ R :=
      div_le_self hR.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    have hdiff' := hdiff.mono (Metric.ball_subset_ball hrad)
    intro z hz
    have hz' : z ∈ Metric.ball (0 : E) ((R / 2 ^ m) / 2) := by
      convert hz using 1 <;> congr 1 <;> rw [pow_succ] <;> ring
    have h := norm_fderiv_le_four_div (by positivity : 0 < R / 2 ^ m) hdiff' hm hz'
    rw [norm_fderiv_iteratedFDeriv] at h
    apply h.trans_eq
    simp only [cauchyFactor, pow_succ]
    field_simp [hR.ne']

end Yau.Proofs.C07Aux
