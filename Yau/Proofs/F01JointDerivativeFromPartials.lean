import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! Actual spatial and clock derivatives, continuous in the joint
variables, give the genuine joint Frechet derivative. This applies
to the spatial-jet tower across a pasted terminal face. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem joint_hasFDerivAt_of_space_time_partials
    (f : E × ℝ → F) (A : E × ℝ → E →L[ℝ] F) (B : E × ℝ → F) (p : E × ℝ)
    (hSpace : ∀ᶠ q in 𝓝 p, HasFDerivAt (fun x => f (x, q.2)) (A q) q.1)
    (hTime : ∀ᶠ q in 𝓝 p, HasDerivAt (fun t => f (q.1, t)) (B q) q.2)
    (hA : ContinuousAt A p) (hB : ContinuousAt B p) :
    HasFDerivAt f ((A p).coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight (B p))) p := by
  have hClock : ∀ᶠ q in 𝓝 p, HasFDerivAt (fun t => f (q.1, t))
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (B q)) q.2 := by
    filter_upwards [hTime] with q hq
    exact hq.hasFDerivAt
  have hClockCont : ContinuousAt
      (fun q => (ContinuousLinearMap.id ℝ ℝ).smulRight (B q)) p :=
    (ContinuousLinearMap.smulRightL ℝ ℝ F (ContinuousLinearMap.id ℝ ℝ)).continuous.continuousAt.comp hB
  have hh := hasStrictFDerivAt_uncurry_coprod
    (f := fun x t => f (x, t)) (f₁ := fun x t => A (x, t))
    (f₂ := fun x t => (ContinuousLinearMap.id ℝ ℝ).smulRight (B (x, t)))
    hSpace hClock hA hClockCont
  exact hh.hasFDerivAt

end Yau.NodeProofs.F01Aux
