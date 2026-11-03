import Yau.Proofs.V03ComplexSlice
import Yau.Proofs.V03EuclideanRadial

/-! The original closed spatial-disc slice has exactly the second
component of the genuine joint within derivative. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem fderivWithin_complex_disc_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set ℂ} {H : ℂ × ℂ → E} {z ζ : ℂ} (hz : z ∈ U)
    (hζ : ζ ∈ Metric.closedBall (0 : ℂ) 1)
    (hH : DifferentiableWithinAt ℂ H (U ×ˢ Metric.closedBall (0 : ℂ) 1) (z, ζ)) (v : ℂ) :
    fderivWithin ℂ (fun η => H (z, η)) (Metric.closedBall (0 : ℂ) 1) ζ v =
      fderivWithin ℂ H (U ×ˢ Metric.closedBall (0 : ℂ) 1) (z, ζ) (0, v) := by
  have hinc : HasFDerivWithinAt (fun η : ℂ => (z, η))
      ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ)) (Metric.closedBall (0 : ℂ) 1) ζ :=
    ((hasFDerivAt_const (𝕜 := ℂ) z ζ).prodMk (hasFDerivAt_id ζ)).hasFDerivWithinAt
  have hmap : Set.MapsTo (fun η : ℂ => (z, η)) (Metric.closedBall (0 : ℂ) 1)
      (U ×ˢ Metric.closedBall (0 : ℂ) 1) := fun η hη => ⟨hz, hη⟩
  have hh := congrArg (fun A : ℂ →L[ℂ] E => A v)
    ((hH.hasFDerivWithinAt.comp ζ hinc hmap).fderivWithin (uniqueDiffOn_complex_closedDisc ζ hζ))
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply] using hh

end Yau.Blueprint.V03Proof
