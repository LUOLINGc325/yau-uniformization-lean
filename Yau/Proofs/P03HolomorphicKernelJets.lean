import Yau.Proofs.P03ComplexScaledKernel
import Yau.Proofs.P03ConvolutionJetBounds
import Yau.Proofs.P03RadialMean

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

/-- The constant depends only on the fixed radial kernel and the derivative
order. The original function and every positive scale are quantified after it. -/
theorem exists_holomorphic_jet_L1_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ComplexVector n → ℂ),
      Continuous f → Integrable f volume → ∀ (a : ComplexVector n) (t : ℝ), 0 < t →
      DifferentiableOn ℂ f (Metric.ball a (3 * t)) →
      ‖iteratedFDeriv ℝ j f a‖ ≤
        ((t ^ Module.finrank ℝ (ComplexVector n))⁻¹ * (t⁻¹) ^ j * C) *
          ∫ y in Metric.closedBall a t, ‖f y‖ := by
  obtain ⟨C, hC, hb⟩ := exists_complexScaledKernel_jet_bound (n := n) j
  refine ⟨C, hC, ?_⟩
  intro f hc hi a t ht hH
  have heq : scalarConvolution f (complexScaledKernel t) =ᶠ[𝓝 a] f := by
    filter_upwards [Metric.ball_mem_nhds a (by linarith : 0 < 2 * t)] with x hx
    rw [scalarConvolution_complexScaledKernel]
    exact radial_smoothing_eq (scaledRadialKernel_contDiff t).continuous
      (scaledRadialKernel_hasCompactSupport ht) (scaledRadialKernel_tsupport_subset ht)
      (scaledRadialKernel_integral ht) (scaledRadialKernel_rotation t) hc hH hx
  rw [← (heq.iteratedFDeriv ℝ j).self_of_nhds]
  exact scalarConvolution_jet_norm_le f (complexScaledKernel t) hi (complexScaledKernel_contDiff t)
    (complexScaledKernel_hasCompactSupport ht) j a t _ (by positivity) (hb t ht)
    (complexScaledKernel_tsupport_subset ht)

end Yau.NodeProofs.P03Aux
