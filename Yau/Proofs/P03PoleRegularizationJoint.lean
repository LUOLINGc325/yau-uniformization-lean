import Yau.Proofs.P03PoleRegularization

open scoped Topology ContDiff

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

/-- The same logarithmic regularization is jointly smooth in space and in
the real parameter, including parameter zero away from the pole. -/
theorem modelLogPole_joint_contDiffOn (a : ComplexVector n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => modelLogPole a p.2 p.1)
      {p | 0 < ‖p.1 - a‖ ^ 2 + p.2} := by
  have hq : ContDiff ℝ ∞ (fun p : ComplexVector n × ℝ => ‖p.1 - a‖ ^ 2 + p.2) :=
    ((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_const)).add contDiff_snd
  exact hq.contDiffOn.log fun p hp => ne_of_gt hp

theorem cutoffPoleRegularization_joint_contDiffOn
    (c : ℝ) (θ : ComplexVector n → ℝ) (hθ : ContDiff ℝ ∞ θ) (a : ComplexVector n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => cutoffPoleRegularization c θ a p.2 p.1)
      {p | 0 < ‖p.1 - a‖ ^ 2 + p.2} :=
  (contDiff_const.mul (hθ.comp contDiff_fst)).contDiffOn.mul (modelLogPole_joint_contDiffOn a)

theorem modelLogPole_continuousAt_epsilon_zero (a z : ComplexVector n) (hz : z ≠ a) :
    ContinuousAt (fun ε : ℝ => modelLogPole a ε z) 0 := by
  have hq : 0 < ‖z - a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz))
  have hn : ‖z - a‖ ^ 2 + (0 : ℝ) ≠ 0 := by simpa only [add_zero] using ne_of_gt hq
  exact (continuousAt_const.add continuousAt_id).log hn

end Yau.NodeProofs.P03Aux
