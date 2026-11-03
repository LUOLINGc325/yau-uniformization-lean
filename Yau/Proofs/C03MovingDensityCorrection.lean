import Yau.Proofs.C03MovingAccelerationDifference

/-! The genuine second energy density changes by the covariant derivative
of the explicit quadratic correction, with the curvature terms unchanged. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem movingEnergyDensity_second_correction (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (γ W : ℝ → ComplexVector n) (Q : ComplexVector n)
    (hγ : ContDiff ℝ 3 γ) (hW : ContDiff ℝ 3 W) (v : ℂ) (t : ℝ)
    (hparallel : HasDerivAt (fun s => v • W s)
      (-chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t) (v • W t)) t) :
    mapDirection (mapDirection (sourceEnergyDensity hn k (movingJoint γ W Q)) (v, 0))
        (v, 0) (0, t) -
      mapDirection (mapDirection (sourceEnergyDensity hn k (movingJoint γ W 0)) (v, 0))
        (v, 0) (0, t) =
      2 * realMetricInChart k (0 : ComplexVector n) (γ t) (deriv γ t)
        (v ^ 2 • Q + chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t)
          (t • (v ^ 2 • Q))) := by
  have hZ (q : ComplexVector n) : ContDiff ℝ 3 (movingJoint γ W q) := by
    apply contDiffOn_univ.mp
    simpa only [Set.univ_prod_univ] using
      movingJoint_contDiffOn γ W q Set.univ hγ.contDiffOn hW.contDiffOn
  let G := realMetricInChart k (0 : ComplexVector n) (γ t) (deriv γ t)
  let Γ := chartChristoffelBilin k (0 : ComplexVector n)
  let C := 2 * G (connectionCurvature Γ (γ t) (v • W t) (deriv γ t) (v • W t))
  have hfull (q : ComplexVector n) :
      mapDirection (mapDirection (sourceEnergyDensity hn k (movingJoint γ W q)) (v, 0))
          (v, 0) (0, t) = C +
        2 * G (mapCovariantD Γ (movingJoint γ W q) (0, 1)
          (movingRadialAcceleration hn k γ W q v) (0, t)) := by
    unfold sourceEnergyDensity
    have hpar := movingJoint_parallel_firstVariation Γ γ W q
      ((hZ q).contDiffAt.of_le (by norm_num)) v hparallel
    have hsym := mapCovariantD_torsionFree Γ (movingJoint γ W q)
      ((hZ q).contDiffAt.of_le (by norm_num))
      (chartChristoffelBilin_symm k (0 : ComplexVector n) (movingJoint γ W q (0, t)))
      (v, 0) (0, 1)
    have hp : mapCovariantD Γ (movingJoint γ W q) (v, 0)
        (mapDirection (movingJoint γ W q) (0, 1)) (0, t) = 0 := hsym.trans hpar
    have H := mapEnergyDensity_full_secondVariation k hk (0 : ComplexVector n)
      (movingJoint γ W q) (p := (0, t)) (by rw [euclidean_chartTarget hn]; trivial)
      (hZ q).contDiffAt (v, 0) (0, 1)
    rw [hp] at H
    simpa only [sourceEnergyDensity, G, Γ, C, movingRadialAcceleration,
      map_zero, zero_apply, mul_zero, zero_add,
      movingJoint_time_jet_zero _ _ _ ((hZ q).differentiable (by norm_num) _),
      movingJoint_parameter_jet _ _ _ ((hZ q).differentiable (by norm_num) _),
      mul_zero, zero_smul, add_zero, movingJoint, movingTrial_zero_parameter] using H
  rw [hfull Q, hfull 0]
  have H := congrArg (fun a : ComplexVector n => 2 * G a)
    (movingRadialAcceleration_difference hn k hk γ W Q hγ hW v t)
  simpa only [map_sub, mul_sub, add_sub_add_left_eq_sub] using H

end Yau.Proofs.C03Aux
