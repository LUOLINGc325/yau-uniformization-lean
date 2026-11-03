import Yau.LeafProofs.L05ChuRestriction
import Yau.LeafProofs.L16LowJetInterpolation

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def chuLowJetBudget (gamma M : ℝ) : ℝ :=
  8*((1/16:ℝ)^(1-gamma)*M+(1/16:ℝ)^(-1-gamma)*M)

theorem chu_coarse_lowJet_holder {n : ℕ} {u : Point n → ℝ} {eta gamma M : ℝ}
    (hg : 0 < gamma) (hg1 : gamma < 1) (hu : SchauderBound eta (backward (3/4)) u M) :
    HolderBound gamma (cylinder (Metric.closedBall 0 (5/8)) (-(1/2)) 0)
      (fun p => (u p,spatialD u p)) (chuLowJetBudget gamma M) := by
  let Q : Set (Point n) := cylinder (Metric.closedBall 0 (11/16)) (-(1/2)) 0
  have hQ : Q ⊆ backward (3/4) := by
    apply L16Aux.cylinder_subset_backward
    · intro x hx
      have hnorm : ‖x‖ ≤ (11/16:ℝ) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
      exact Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hnorm.trans_lt (by norm_num : (11/16:ℝ) < 3/4))
    · norm_num
    · exact le_rfl
  have hC2 : C2 Q u := chu_c2_cylinder_restrict_backward (by norm_num) hQ hu.1
  have hSup (p : Point n) (hp : p ∈ Q) : |u p| ≤ M := (hu.2.2.1 p (hQ hp)).1
  have hJets (p : Point n) (hp : p ∈ Q) : ‖spatialDD u p‖ ≤ M ∧ |timeD Q u p| ≤ M := by
    refine ⟨hu.2.2.2.1.2.1 p (hQ hp),?_⟩
    rw [chu_timeD_cylinder_restrict_backward (by norm_num) hQ hu.1 hp]
    simpa only [Real.norm_eq_abs] using hu.2.2.2.2.2.1 p (hQ hp)
  exact L16Aux.c2_lowPair_interpolation hg hg1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hu.2.1 hu.2.1 hC2 hSup hJets

end Yau.LeafProofs.L05Aux
