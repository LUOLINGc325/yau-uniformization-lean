import Yau.Proofs.F01ShiftedNativePotential

/-! Smoothness on every genuine compact subhorizon gives ordinary joint
smoothness on the open partial-flow domain, without a terminal extension. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem partial_bounded_chart_joint_smooth
    (A : BoundedChartFamily g) (U : M.Carrier → ℝ → ℝ) (Tstar : ℝ)
    (hU : ∀ T, 0 ≤ T → T < Tstar → SmoothSpaceTime U (Icc 0 T)) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (fun p : Point n => U (A.chart a p.1) p.2)
      (ball 0 A.radius ×ˢ Ioo 0 Tstar) := by
  intro p hp
  let τ : ℝ := (p.2 + Tstar) / 2
  have ht : p.2 < τ := by dsimp only [τ]; linarith [hp.2.2]
  have hτ : τ < Tstar := by dsimp only [τ]; linarith [hp.2.2]
  have hτ0 : 0 ≤ τ := (hp.2.1.trans ht).le
  have hLocal := bounded_chart_spaceTime_smooth A (hU τ hτ0 hτ) a
  have hN : ball (0 : Space n) A.radius ×ˢ Icc 0 τ ∈ 𝓝 p :=
    mem_of_superset ((isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hp.1, hp.2.1, ht⟩)
      (prod_mono Subset.rfl Ioo_subset_Icc_self)
  exact (hLocal.contDiffAt hN).contDiffWithinAt

theorem partial_terminal_shifted_potential_smooth
    (A : BoundedChartFamily g) (U : M.Carrier → ℝ → ℝ)
    {ρ Tstar : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius)
    (hEarly : 0 ≤ Tstar - ρ ^ 2 / 4)
    (hU : ∀ T, 0 ≤ T → T < Tstar → SmoothSpaceTime U (Icc 0 T)) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (shiftedNativePotential A U a ρ Tstar)
      (ball 0 1 ×ˢ Ioo (-(1 / 4 : ℝ)) 0) := by
  have hAffine : ContDiff ℝ ∞ (affineParabolicPoint (n := n) ρ 0 Tstar) := by
    unfold affineParabolicPoint
    fun_prop
  apply contDiffOn_const.mul
  apply (partial_bounded_chart_joint_smooth A U Tstar hU a).comp hAffine.contDiffOn
  intro p hp
  refine ⟨shifted_space_maps A hρ hρr hp.1, ?_, ?_⟩
  · have hh := mul_lt_mul_of_pos_left hp.2.1 (sq_pos_of_pos hρ)
    change 0 < Tstar + ρ ^ 2 * p.2
    linarith
  · change Tstar + ρ ^ 2 * p.2 < Tstar
    exact add_lt_of_neg_right Tstar (mul_neg_of_pos_of_neg (sq_pos_of_pos hρ) hp.2.2)

end Yau.NodeProofs.F01Aux
