import Yau.Proofs.C03MovingAcceleration

/-! The actual covariant acceleration changes by precisely the prescribed
linear-in-time vector when the terminal holomorphic second jet changes. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def movingRadialAcceleration (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn))
    (γ W : ℝ → ComplexVector n) (Q : ComplexVector n) (v : ℂ) :
    ℂ × ℝ → ComplexVector n :=
  mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) (movingJoint γ W Q) (v, 0)
    (mapDirection (movingJoint γ W Q) (v, 0))

theorem movingRadialAcceleration_contDiff (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (γ W : ℝ → ComplexVector n) (Q : ComplexVector n)
    (hγ : ContDiff ℝ 3 γ) (hW : ContDiff ℝ 3 W) (v : ℂ) :
    ContDiff ℝ 1 (movingRadialAcceleration hn k γ W Q v) := by
  have hZ : ContDiff ℝ 3 (movingJoint γ W Q) := by
    apply contDiffOn_univ.mp
    simpa only [Set.univ_prod_univ] using
      movingJoint_contDiffOn γ W Q Set.univ hγ.contDiffOn hW.contDiffOn
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact mapCovariantD_contDiffAt k hk (0 : ComplexVector n) (movingJoint γ W Q) _
    (by rw [euclidean_chartTarget hn]; trivial) 1 (hZ.contDiffAt.of_le (by norm_num))
    (mapDirection_contDiffAt _ 2 hZ.contDiffAt (v, 0)) (v, 0)

theorem movingRadialAcceleration_difference (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (γ W : ℝ → ComplexVector n) (Q : ComplexVector n)
    (hγ : ContDiff ℝ 3 γ) (hW : ContDiff ℝ 3 W) (v : ℂ) (t : ℝ) :
    mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) (movingJoint γ W Q)
        (0, 1) (movingRadialAcceleration hn k γ W Q v) (0, t) -
      mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) (movingJoint γ W 0)
        (0, 1) (movingRadialAcceleration hn k γ W 0 v) (0, t) =
      v ^ 2 • Q + chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t)
        (t • (v ^ 2 • Q)) := by
  have hZ (q : ComplexVector n) : ContDiff ℝ 3 (movingJoint γ W q) := by
    apply contDiffOn_univ.mp
    simpa only [Set.univ_prod_univ] using
      movingJoint_contDiffOn γ W q Set.univ hγ.contDiffOn hW.contDiffOn
  have HA : (fun s => movingRadialAcceleration hn k γ W Q v (0, s)) =ᶠ[𝓝 t]
      (fun s => movingRadialAcceleration hn k γ W 0 v (0, s) + s • (v ^ 2 • Q)) := by
    apply Filter.Eventually.of_forall
    intro s
    dsimp only [movingRadialAcceleration]
    rw [movingJoint_radial_acceleration_zero_parameter _ γ W Q
      ((hZ Q).contDiffAt.of_le (by norm_num)),
      movingJoint_radial_acceleration_zero_parameter _ γ W 0
        ((hZ 0).contDiffAt.of_le (by norm_num))]
    simp only [smul_zero, zero_add]
    exact add_comm _ _
  have H := covariant_time_difference_of_germ
    (chartChristoffelBilin k (0 : ComplexVector n)) (movingJoint γ W Q) (movingJoint γ W 0)
    (movingRadialAcceleration hn k γ W Q v) (movingRadialAcceleration hn k γ W 0 v)
    (v ^ 2 • Q) t
    ((movingRadialAcceleration_contDiff hn k hk γ W Q hγ hW v).differentiable (by norm_num) _)
    ((movingRadialAcceleration_contDiff hn k hk γ W 0 hγ hW v).differentiable (by norm_num) _)
    (by simp only [movingJoint, movingTrial_zero_parameter])
    (by rw [movingJoint_time_jet_zero _ _ _ ((hZ Q).differentiable (by norm_num) _),
      movingJoint_time_jet_zero _ _ _ ((hZ 0).differentiable (by norm_num) _)]) HA
  simpa only [movingJoint_time_jet_zero _ _ _ ((hZ 0).differentiable (by norm_num) _),
    movingJoint, movingTrial_zero_parameter] using H

end Yau.Proofs.C03Aux
