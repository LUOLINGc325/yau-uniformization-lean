import Yau.Proofs.C03MovingEnergyJets
import Yau.LeafProofs.L23LocalDistanceSupportEnergyAdmissible

/-! Every actual polynomial trial path bounds the distance of its moving
endpoints by its actual source-field energy. -/

noncomputable section
open Set
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem movingEnergy_bounds_distance (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (γ W : ℝ → ComplexVector n) (Q : ComplexVector n)
    (hγ : ContDiff ℝ 3 γ) (hW : ContDiff ℝ 3 W) (a : ℂ) :
    inducedDistance k (γ 0 + a • W 0)
      (γ 1 + a • W 1 + ((1 / 2 : ℂ) * a ^ 2) • Q) ^ 2 ≤
        sourceEnergy hn k (movingJoint γ W Q) a := by
  letI := manifold_realSmooth (ComplexEuclideanManifold n hn)
  have hZ : ContDiff ℝ 3 (movingJoint γ W Q) := by
    apply contDiffOn_univ.mp
    simpa only [univ_prod_univ] using
      movingJoint_contDiffOn γ W Q univ hγ.contDiffOn hW.contDiffOn
  have hpath : ContDiff ℝ 1 (fun t => movingTrial γ W Q t a) :=
    ((hZ.of_le (by norm_num)).comp (contDiff_const.prodMk contDiff_id))
  have hM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1
      (fun t : ℝ => movingTrial γ W Q t a) := hpath.contMDiff
  have hMOn : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1
      (fun t : ℝ => movingTrial γ W Q t a) (Ioo (-1) (1 + 1)) := hM.contMDiffOn
  let β : ℝ → ComplexVector n := fun t => movingTrial γ W Q t a
  have H := inducedDistance_sq_le_fieldPathEnergy_of_contMDiffOn k hk β 1 zero_lt_one hMOn
  have HE := sourceEnergy_eq_fieldPathEnergy hn k (movingJoint γ W Q) a
    (fun t _ => hZ.differentiable (by norm_num) (a, t))
  rw [HE]
  simpa only [β, movingJoint, movingTrial_initial, movingTrial_terminal] using H

theorem movingEnergy_zero (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn))
    (γ W : ℝ → ComplexVector n) (Q : ComplexVector n)
    (hγ : ContDiff ℝ 3 γ) (hW : ContDiff ℝ 3 W) (D : ℝ)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1, L23LocalDistanceContract.actualSpeedSq k γ t = D) :
    sourceEnergy hn k (movingJoint γ W Q) 0 = D := by
  have hZ : ContDiff ℝ 3 (movingJoint γ W Q) := by
    apply contDiffOn_univ.mp
    simpa only [univ_prod_univ] using
      movingJoint_contDiffOn γ W Q univ hγ.contDiffOn hW.contDiffOn
  rw [sourceEnergy_eq_fieldPathEnergy hn k (movingJoint γ W Q) 0
    (fun t _ => hZ.differentiable (by norm_num) (0, t))]
  have heq : (fun t => movingJoint γ W Q (0, t)) = γ := by
    funext t
    exact movingTrial_zero_parameter γ W Q t
  rw [heq]
  exact fieldPathEnergy_eq_of_constant_actualSpeedSq k γ D hspeed

end Yau.Proofs.C03Aux
