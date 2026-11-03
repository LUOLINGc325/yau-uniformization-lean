import Yau.Proofs.P03PoleAnnulusBounds
import Yau.Proofs.P03LogPolePositivity
import Yau.LeafProofs.L22LeviCalculus

open scoped Topology ContDiff
open Filter Set Metric

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs.L22Aux

theorem complexLeviQuadratic_congr_germ {n : ℕ} {f g : ComplexVector n → ℝ}
    {z : ComplexVector n} (hfg : f =ᶠ[𝓝 z] g) (v : ComplexVector n) :
    complexLeviQuadratic f z v = complexLeviQuadratic g z v := by
  have hd := (hfg.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  simp only [complexLeviQuadratic, hd]

/-- The cutoff logarithm is plurisubharmonic off one fixed compact annulus. -/
theorem cutoffPole_complexLevi_nonneg_off_annulus {n : ℕ}
    (a z v : ComplexVector n) (b : ContDiffBump a) (c : ℝ) (hc : 0 ≤ c)
    {ε : ℝ} (hε : 0 < ε)
    (hz : z ∉ closedBall a b.rOut \ ball a b.rIn) :
    0 ≤ complexLeviQuadratic (cutoffPoleRegularization c b a ε) z v := by
  by_cases hout : z ∈ closedBall a b.rOut
  · have hin : z ∈ ball a b.rIn := by
      by_contra hn
      exact hz ⟨hout, hn⟩
    have he : cutoffPoleRegularization c b a ε =ᶠ[𝓝 z]
        (fun y => c * modelLogPole a ε y) := by
      filter_upwards [b.eventuallyEq_one_of_mem_ball hin] with y hy
      simp only [cutoffPoleRegularization, hy, Pi.one_apply, mul_one]
    rw [complexLeviQuadratic_congr_germ he,
      complexLeviQuadratic_const_mul ((modelLogPole_contDiff a hε).contDiffAt.of_le (by simp))]
    exact mul_nonneg hc (modelLogPole_complexLevi_nonneg a z v hε)
  · have hb : (b : ComplexVector n → ℝ) =ᶠ[𝓝 z] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (by simpa only [b.tsupport_eq] using hout)
    have he : cutoffPoleRegularization c b a ε =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hb] with y hy
      simp only [cutoffPoleRegularization, hy, Pi.zero_apply, mul_zero, zero_mul]
    rw [complexLeviQuadratic_congr_germ he, complexLeviQuadratic_zero]

/-- One finite negative bound works globally for the entire sequence. Only
the fixed compact annulus contributes a negative cutoff error. -/
theorem exists_cutoffPole_uniform_levi_lower {n : ℕ}
    (a : ComplexVector n) (b : ContDiffBump a) (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, ∀ z v : ComplexVector n,
      -C * ‖v‖ ^ 2 ≤
        complexLeviQuadratic (cutoffPoleRegularization c b a (poleEpsilon j)) z v := by
  let K := closedBall a b.rOut \ ball a b.rIn
  have hK : IsCompact K := (isCompact_closedBall a b.rOut).diff isOpen_ball
  have ha : a ∉ K := by
    intro h
    exact h.2 (mem_ball_self b.rIn_pos)
  obtain ⟨C, hC, hbound⟩ := exists_uniform_cutoffPole_levi_bound_away
    c b b.contDiff a hK ha (1 / 4) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro j z v
  by_cases hz : z ∈ K
  · have hh := (abs_le.mp (hbound (poleEpsilon j)
      ⟨(poleEpsilon_pos j).le, poleEpsilon_le_quarter j⟩ z hz v)).1
    simpa only [neg_mul] using hh
  · exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC) (sq_nonneg _)).trans
      (cutoffPole_complexLevi_nonneg_off_annulus a z v b c hc (poleEpsilon_pos j) hz)

end Yau.NodeProofs.P03Aux
