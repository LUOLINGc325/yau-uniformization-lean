import Yau.Proofs.C03TargetPoleBasic

/-! The actual normalized sequence has the expected punctured and singular limits. -/
noncomputable section
open scoped Topology ContDiff
open Set Filter Metric
namespace Yau.Proofs.C03Aux.TargetPole
open Yau Yau.NodeProofs.P03Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem pole_tendsto_away (delta : ℝ) (hdelta : 0 < delta) (m : ℕ)
    {w : ComplexVector n} (hw : w ≠ 0) :
    Tendsto (fun j => pole delta hdelta m j w) atTop
      (𝓝 ((m : ℝ) * cutoff delta hdelta w *
        (Real.log (‖w‖ ^ 2) - Real.log (1 + delta ^ 2)))) := by
  have H := ((modelLogPole_sequence_tendsto_away (0 : ComplexVector n) w hw).sub_const
    (Real.log (1 + delta ^ 2))).const_mul ((m : ℝ) * cutoff delta hdelta w)
  simpa only [pole, regularizedPole, sub_zero] using H

theorem pole_zero_tendsto_atBot (delta : ℝ) (hdelta : 0 < delta) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun j => pole (n := n) delta hdelta m j 0) atTop atBot := by
  have heps : Tendsto poleEpsilon atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨poleEpsilon_tendsto_zero,
      Eventually.of_forall (fun j => poleEpsilon_pos j)⟩
  have hlog := Real.tendsto_log_nhdsGT_zero.comp heps
  have hsub := tendsto_atBot_add_const_right atTop (-Real.log (1 + delta ^ 2)) hlog
  have H := Tendsto.const_mul_atBot (by exact_mod_cast hm : (0 : ℝ) < m) hsub
  have hb : cutoff (n := n) delta hdelta 0 = 1 :=
    (cutoff delta hdelta).one_of_mem_closedBall (mem_closedBall_self (half_pos hdelta).le)
  simpa only [pole, regularizedPole, hb, mul_one, modelLogPole, sub_self, norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, sub_eq_add_neg, Function.comp_def] using H

end Yau.Proofs.C03Aux.TargetPole
