import Yau.Proofs.P03PoleSequence

/-! The actual normalized cutoff logarithmic pole sequence in all dimensions. -/
noncomputable section
open scoped Topology ContDiff
open Set Filter Metric
namespace Yau.Proofs.C03Aux.TargetPole
open Yau Yau.NodeProofs.P03Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def cutoff (delta : ℝ) (hdelta : 0 < delta) : ContDiffBump (0 : ComplexVector n) :=
  ⟨delta / 2, delta, by positivity, by linarith⟩

def regularizedPole (delta : ℝ) (hdelta : 0 < delta) (m : ℕ) (epsilon : ℝ)
    (w : ComplexVector n) : ℝ :=
  (m : ℝ) * cutoff delta hdelta w *
    (modelLogPole 0 epsilon w - Real.log (1 + delta ^ 2))

def pole (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ) (w : ComplexVector n) : ℝ :=
  regularizedPole delta hdelta m (poleEpsilon j) w

theorem regularizedPole_ratio (delta : ℝ) (hdelta : 0 < delta) (m : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (w : ComplexVector n) :
    regularizedPole delta hdelta m epsilon w =
      (m : ℝ) * cutoff delta hdelta w *
        Real.log ((‖w‖ ^ 2 + epsilon) / (1 + delta ^ 2)) := by
  rw [Real.log_div (ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hepsilon))
    (ne_of_gt (by positivity : 0 < 1 + delta ^ 2))]
  simp only [regularizedPole, modelLogPole, sub_zero]

theorem regularizedPole_contDiff (delta : ℝ) (hdelta : 0 < delta) (m : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ContDiff ℝ ∞ (regularizedPole (n := n) delta hdelta m epsilon) :=
  (contDiff_const.mul (cutoff delta hdelta).contDiff).mul
    ((modelLogPole_contDiff 0 hepsilon).sub contDiff_const)

theorem pole_contDiff (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ) :
    ContDiff ℝ ∞ (pole (n := n) delta hdelta m j) :=
  regularizedPole_contDiff delta hdelta m (poleEpsilon_pos j)

theorem pole_tsupport_subset (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ) :
    tsupport (pole (n := n) delta hdelta m j) ⊆ closedBall 0 delta := by
  apply closure_minimal _ isClosed_closedBall
  intro w hw
  have hb : cutoff delta hdelta w ≠ 0 := by
    intro he
    exact hw (by simp [pole, regularizedPole, he])
  have hw' : w ∈ Function.support (cutoff (n := n) delta hdelta) := hb
  rw [(cutoff delta hdelta).support_eq] at hw'
  exact (mem_ball.mp hw').le

theorem pole_hasCompactSupport (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ) :
    HasCompactSupport (pole (n := n) delta hdelta m j) :=
  (isCompact_closedBall (0 : ComplexVector n) delta).of_isClosed_subset
    (isClosed_tsupport _) (pole_tsupport_subset delta hdelta m j)

theorem pole_nonpos (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ)
    (w : ComplexVector n) : pole delta hdelta m j w ≤ 0 := by
  by_cases hb : cutoff delta hdelta w = 0
  · simp [pole, regularizedPole, hb]
  · have hw : w ∈ ball 0 delta := by
      have H : w ∈ Function.support (cutoff delta hdelta) := hb
      rw [(cutoff delta hdelta).support_eq] at H
      exact H
    have hn : ‖w‖ < delta := by simpa only [mem_ball, dist_zero_right] using hw
    have hepsilon := poleEpsilon_le_quarter j
    have hq : ‖w‖ ^ 2 + poleEpsilon j ≤ 1 + delta ^ 2 := by
      nlinarith [norm_nonneg w]
    have hlog := Real.log_le_log
      (add_pos_of_nonneg_of_pos (sq_nonneg ‖w‖) (poleEpsilon_pos j)) hq
    apply mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Nat.cast_nonneg m) (cutoff delta hdelta).nonneg)
    change modelLogPole 0 (poleEpsilon j) w - Real.log (1 + delta ^ 2) ≤ 0
    simpa only [modelLogPole, sub_zero, sub_nonpos] using hlog

theorem pole_antitone (delta : ℝ) (hdelta : 0 < delta) (m : ℕ)
    (w : ComplexVector n) : Antitone (fun j => pole delta hdelta m j w) := by
  intro i j hij
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Nat.cast_nonneg m) (cutoff delta hdelta).nonneg)
  exact sub_le_sub_right
    (modelLogPole_mono_epsilon 0 w (poleEpsilon_pos j) (poleEpsilon_antitone hij)) _

theorem pole_eq_on_inner (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ)
    {w : ComplexVector n} (hw : w ∈ closedBall 0 (delta / 2)) :
    pole delta hdelta m j w =
      (m : ℝ) * (Real.log (‖w‖ ^ 2 + poleEpsilon j) - Real.log (1 + delta ^ 2)) := by
  have hb : cutoff delta hdelta w = 1 := (cutoff delta hdelta).one_of_mem_closedBall hw
  simp only [pole, regularizedPole, hb, mul_one, modelLogPole, sub_zero]

theorem pole_germ_at_zero (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ) :
    pole (n := n) delta hdelta m j =ᶠ[𝓝 0]
      (fun w => (m : ℝ) *
        (Real.log (‖w‖ ^ 2 + poleEpsilon j) - Real.log (1 + delta ^ 2))) := by
  filter_upwards [(cutoff (n := n) delta hdelta).eventuallyEq_one] with w hw
  simp only [pole, regularizedPole, hw, Pi.one_apply, mul_one, modelLogPole, sub_zero]

theorem pole_zero_germ_outside (delta : ℝ) (hdelta : 0 < delta) (m j : ℕ)
    {w : ComplexVector n} (hw : w ∉ closedBall 0 delta) :
    pole delta hdelta m j =ᶠ[𝓝 w] (fun _ => 0) :=
  notMem_tsupport_iff_eventuallyEq.mp
    (fun H => hw (pole_tsupport_subset delta hdelta m j H))

end Yau.Proofs.C03Aux.TargetPole
