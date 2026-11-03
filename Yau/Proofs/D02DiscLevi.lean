import Yau.Proofs.D02HolomorphicPullback
import Yau.Proofs.B01Coordinate

/-! The original closed-disc predicate gives the actual open-disc pullback
regularity in the one-dimensional model used by D04. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def discModelMap (f : ℂ → M.Carrier) (z : ComplexVector 1) : M.Carrier :=
  f (Yau.Proofs.B01Aux.complexOneEquiv.symm z)

theorem discModelMap_contMDiffOn {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) :
    ContMDiffOn (ComplexModel 1) (ComplexModel n) ∞ (discModelMap f)
      (Metric.ball (0 : ComplexVector 1) 1) := by
  have he : ContMDiff (ComplexModel 1) 𝓘(ℂ, ℂ) ∞ Yau.Proofs.B01Aux.complexOneEquiv.symm :=
    Yau.Proofs.B01Aux.complexOneEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff
  apply hf.comp he.contMDiffOn
  intro z hz
  change Yau.Proofs.B01Aux.complexOneEquiv.symm z ∈ Metric.closedBall (0 : ℂ) 1
  simp only [Metric.mem_closedBall, dist_zero_right,
    Yau.Proofs.B01Aux.complexOneEquiv.symm.norm_map]
  exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hz)

theorem smoothFn_disc_continuousOn {u : M.Carrier → ℝ} (hu : SmoothFn u)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) :
    ContinuousOn (fun z => u (f z)) (Metric.closedBall (0 : ℂ) 1) :=
  (L18Aux.continuous_of_smoothFn hu).comp_continuousOn hf.continuousOn

theorem smoothLevi_disc_model {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (hL : ∀ y, (levi u y).PosSemidef) {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f)
    (z : ComplexVector 1) (hz : z ∈ Metric.ball (0 : ComplexVector 1) 1) :
    ContDiffAt ℝ 2 (fun w => u (discModelMap f w)) z ∧
      ∀ v, 0 ≤ L22Aux.complexLeviQuadratic (fun w => u (discModelMap f w)) z v :=
  smoothLevi_holomorphicPullback Metric.isOpen_ball u hu hL (discModelMap f)
    (discModelMap_contMDiffOn hf) z hz

end Yau.NodeProofs.D02Aux
