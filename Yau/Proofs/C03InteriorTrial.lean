import Yau.Proofs.C03MovingEnergyDistance
import Yau.Proofs.C03EnergyTaylor

/-! An interior distance bound leaves an open energy margin. The explicit
holomorphic trial with zero quadratic correction is admissible near zero. -/

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem moving_trial_admissible_of_energy_margin (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (γ W : ℝ → ComplexVector n) (hγ : ContDiff ℝ 3 γ) (hW : ContDiff ℝ 3 W)
    (D ρ : ℝ) (hρ : 0 < ρ) (hmargin : D ^ 2 < ρ ^ 2)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1, actualSpeedSq k γ t = D ^ 2) :
    ∀ᶠ a : ℂ in 𝓝 0,
      inducedDistance k (γ 0 + a • W 0) (γ 1 + a • W 1) ≤ ρ := by
  let F := sourceEnergy hn k (movingJoint γ W 0)
  have hF : ContDiff ℝ 2 F := by
    apply contDiffOn_univ.mp
    exact sourceEnergy_contDiffOn hn k hk _ univ univ isOpen_univ isOpen_univ (subset_univ _)
      (movingJoint_contDiffOn γ W 0 univ hγ.contDiffOn hW.contDiffOn)
  have hzero : F 0 = D ^ 2 := movingEnergy_zero hn k γ W 0 hγ hW (D ^ 2) hspeed
  have hnear : ∀ᶠ a : ℂ in 𝓝 0, F a < ρ ^ 2 :=
    hF.continuous.continuousAt.eventually_lt_const (by rw [hzero]; exact hmargin)
  filter_upwards [hnear] with a ha
  have hbound := movingEnergy_bounds_distance hn k hk γ W 0 hγ hW a
  simp only [smul_zero, add_zero] at hbound
  exact (distance_lt_radius_of_energy_lt hρ hbound ha).le

end Yau.Proofs.C03Aux
