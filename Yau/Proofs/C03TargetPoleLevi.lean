import Yau.Proofs.C03TargetPoleBasic
import Yau.Proofs.P03CutoffPoleLevi

/-! A single finite Levi lower bound precedes every regularization index. -/
noncomputable section
open scoped Topology ContDiff
open Set Filter Metric
namespace Yau.Proofs.C03Aux.TargetPole
open Yau Yau.NodeProofs.P03Aux Yau.LeafProofs.L22Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def cutoffCorrection (delta : ℝ) (hdelta : 0 < delta) (m : ℕ)
    (w : ComplexVector n) : ℝ :=
  ((m : ℝ) * Real.log (1 + delta ^ 2)) * cutoff delta hdelta w

theorem cutoffCorrection_contDiff (delta : ℝ) (hdelta : 0 < delta) (m : ℕ) :
    ContDiff ℝ ∞ (cutoffCorrection (n := n) delta hdelta m) :=
  contDiff_const.mul (cutoff delta hdelta).contDiff

theorem exists_cutoffCorrection_uniform_levi_bound (delta : ℝ) (hdelta : 0 < delta)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w v : ComplexVector n,
      |complexLeviQuadratic (cutoffCorrection delta hdelta m) w v| ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_levi_bound_on_compact isOpen_univ
    (cutoffCorrection_contDiff (n := n) delta hdelta m).contDiffOn
    (isCompact_closedBall (0 : ComplexVector n) delta) (subset_univ _)
  refine ⟨C, hC, ?_⟩
  intro w v
  by_cases hw : w ∈ closedBall 0 delta
  · exact hbound w hw v
  · have hb : (cutoff (n := n) delta hdelta : ComplexVector n → ℝ) =ᶠ[𝓝 w] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (by
        rw [(cutoff delta hdelta).tsupport_eq]
        exact hw)
    have hg : cutoffCorrection delta hdelta m =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [hb] with y hy
      simp only [cutoffCorrection, hy, Pi.zero_apply, mul_zero]
    rw [complexLeviQuadratic_congr_germ hg, complexLeviQuadratic_zero, abs_zero]
    exact mul_nonneg hC (sq_nonneg _)

theorem pole_eq_cutoffPole_sub_correction (delta : ℝ) (hdelta : 0 < delta)
    (m j : ℕ) : pole (n := n) delta hdelta m j =
      (fun w => cutoffPoleRegularization (m : ℝ) (cutoff delta hdelta) 0 (poleEpsilon j) w +
        (-1) * cutoffCorrection delta hdelta m w) := by
  funext w
  unfold pole regularizedPole cutoffPoleRegularization cutoffCorrection
  ring

theorem exists_pole_uniform_levi_lower (delta : ℝ) (hdelta : 0 < delta) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, ∀ w v : ComplexVector n,
      -C * ‖v‖ ^ 2 ≤ complexLeviQuadratic (pole delta hdelta m j) w v := by
  obtain ⟨C0, hC0, h0⟩ := exists_cutoffPole_uniform_levi_lower
    (0 : ComplexVector n) (cutoff delta hdelta) (m : ℝ) (Nat.cast_nonneg m)
  obtain ⟨C1, hC1, h1⟩ := exists_cutoffCorrection_uniform_levi_bound
    (n := n) delta hdelta m
  refine ⟨C0 + C1, add_nonneg hC0 hC1, ?_⟩
  intro j w v
  have hA : ContDiffAt ℝ 2
      (cutoffPoleRegularization (m : ℝ) (cutoff delta hdelta) 0 (poleEpsilon j)) w :=
    (cutoffPoleRegularization_contDiff (m : ℝ) (cutoff delta hdelta)
      (cutoff delta hdelta).contDiff 0 (poleEpsilon_pos j)).contDiffAt.of_le (by simp)
  have hB : ContDiffAt ℝ 2 (cutoffCorrection delta hdelta m) w :=
    (cutoffCorrection_contDiff delta hdelta m).contDiffAt.of_le (by simp)
  rw [pole_eq_cutoffPole_sub_correction,
    complexLeviQuadratic_add hA (contDiffAt_const.mul hB),
    complexLeviQuadratic_const_mul hB]
  have H0 := h0 j w v
  have H1 := (abs_le.mp (h1 w v)).2
  nlinarith

end Yau.Proofs.C03Aux.TargetPole
