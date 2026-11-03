import Yau.Proofs.V03HolomorphicDirichletDerivative
import Yau.Proofs.V03ScalarAreaFourier

/-! The actual parameter velocity of a joint holomorphic closed-disc
family is itself smooth on the original closed disc and has finite native
boundary seminorm. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem jointParameterVelocity_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ U) (v : ℂ) :
    ContDiffOn ℂ ∞ (jointParameterVelocity H U z v) (Metric.closedBall (0 : ℂ) 1) := by
  have hS : UniqueDiffOn ℂ (U ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    hU.uniqueDiffOn.prod uniqueDiffOn_complex_closedDisc
  have hD : ContDiffOn ℂ ∞ (fun p => fderivWithin ℂ H
      (U ×ˢ Metric.closedBall (0 : ℂ) 1) p (v, 0)) (U ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    (hH.fderivWithin hS (m := ∞) (by simp)).clm_apply contDiffOn_const
  exact hD.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun ζ hζ => ⟨hz, hζ⟩)

theorem jointParameterVelocity_eq_parameter_derivative {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z ζ : ℂ} (hz : z ∈ U) (hζ : ζ ∈ Metric.closedBall (0 : ℂ) 1) (v : ℂ) :
    jointParameterVelocity H U z v ζ = fderiv ℂ (fun p => H (p, ζ)) z v :=
  (fderiv_complex_parameter_slice hU hz hζ ((hH.differentiableOn (by simp)) _ ⟨hz, hζ⟩) v).symm

theorem jointParameterVelocity_boundaryDSq_ne_top {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ U) (v : ℂ) :
    boundaryDSq (fun θ (_ : Unit) => jointParameterVelocity H U z v (circlePoint θ)) ≠ ⊤ := by
  have hf := jointParameterVelocity_contDiffOn hU hH hz v
  rw [boundaryDSq_scalar_eq_inverse_area hf]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (normDiscArea_ne_top_of_closedDisc hf)

end Yau.Blueprint.V03Proof
