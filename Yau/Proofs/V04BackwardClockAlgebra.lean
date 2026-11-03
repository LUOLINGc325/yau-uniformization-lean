import Yau.Proofs.V03Elementary

/-! Exact physical-time algebra for the frozen backward clock. No clock
weight is recomputed after changing the center time. -/

open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem backwardClock_discTime_factor (F : VariationDisc X) (Γ : ℂ → ℂ) {s' : ℝ}
    (hF : 0 < F.s) (hs' : 0 < s') (z : ℂ) :
    discTime (backwardClock F Γ s') z =
      discTime F z * Real.exp (Real.log (s' / F.s) * (1 + (Γ z).re)) := by
  have hratio : 0 < s' / F.s := div_pos hs' hF
  have hhalf : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have hhalfim : ((1 / 2 : ℂ)).im = 0 := by norm_num
  have hre : 2 * (F.w z + (1 / 2 : ℂ) * Real.log (s' / F.s) * Γ z).re =
      2 * (F.w z).re + Real.log (s' / F.s) * (Γ z).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, hhalf, hhalfim, zero_mul, mul_zero, sub_zero, add_zero]
    ring
  unfold discTime backwardClock
  rw [hre, Real.exp_add]
  rw [show Real.log (s' / F.s) * (1 + (Γ z).re) =
    Real.log (s' / F.s) + Real.log (s' / F.s) * (Γ z).re by ring,
    Real.exp_add, Real.exp_log hratio]
  field_simp
  <;> ring

theorem backwardClock_discTime_le (F : VariationDisc X) (Γ : ℂ → ℂ) {s' : ℝ}
    (hF : 0 < F.s) (hs' : 0 < s') (hsF : s' ≤ F.s)
    (hβ : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ 1 + (Γ z).re) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      discTime (backwardClock F Γ s') z ≤ discTime F z := by
  have hratio : 0 < s' / F.s := div_pos hs' hF
  have hlog : Real.log (s' / F.s) ≤ 0 :=
    Real.log_nonpos hratio.le ((div_le_one hF).2 hsF)
  intro z hz
  rw [backwardClock_discTime_factor F Γ hF hs']
  apply mul_le_of_le_one_right (discTime_pos hF z).le
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg hlog (hβ z hz)

theorem backwardClock_boundary_time {d : VariationData X q} {k : ClockData X} {j a : ℕ}
    {F : VariationDisc X} {Γ : ℂ → ℂ} (hΓ : ClockLift d k j a F Γ)
    (hF : 0 < F.s) {s' : ℝ} (hs' : 0 < s') (θ : ℝ) :
    discTime (backwardClock F Γ s') (circlePoint θ) =
      discTime F (circlePoint θ) * (s' / F.s) ^ (clockWeight d k j a F θ) := by
  rw [backwardClock_discTime_factor F Γ hF hs', hΓ.2.2 θ]
  rw [show 1 + (clockWeight d k j a F θ - 1) = clockWeight d k j a F θ by ring,
    Real.rpow_def_of_pos (div_pos hs' hF)]

theorem backwardClock_smooth_center {F : VariationDisc X} {Γ : ℂ → ℂ}
    (hw : ContDiffOn ℂ ∞ F.w (Metric.closedBall (0 : ℂ) 1)) (hw0 : F.w 0 = 0)
    (hΓ : ContDiffOn ℂ ∞ Γ (Metric.closedBall (0 : ℂ) 1)) (hΓ0 : Γ 0 = 0) (s' : ℝ) :
    ContDiffOn ℂ ∞ (backwardClock F Γ s').w (Metric.closedBall (0 : ℂ) 1) ∧
      (backwardClock F Γ s').w 0 = 0 := by
  constructor
  · exact hw.add (contDiffOn_const.mul hΓ)
  · simp [backwardClock, hw0, hΓ0]

end Yau.Blueprint.V04Proof
