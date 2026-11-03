import Yau.Proofs.V03ClosedJTwoFormLaplacian
import Yau.Proofs.V03DiscIntegralVariation
import Yau.Proofs.V03WithinSecondPartial
import Yau.Proofs.V03DiscLaplacianGreen

/-! The actual mixed variation of a closed invariant two-form's disc
integral is exactly its boundary radial current. No parameter acceleration
or extension past the original circle is assumed. -/

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem discDensity_slice_integrable {U : Set ℂ} {f : ℂ × ℂ → ℝ}
    (hf : ContinuousOn f (U ×ˢ ClosedDiscTraceDomain)) {z : ℂ} (hz : z ∈ U) :
    IntegrableOn (fun ζ => f (z, ζ)) (Metric.ball (0 : ℂ) 1) := by
  have hc : ContinuousOn (fun ζ => f (z, ζ)) ClosedDiscTraceDomain :=
    hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun ζ hζ => ⟨hz, hζ⟩)
  exact (hc.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall

theorem mixedReal_closedJForm_discIntegral_eq_current {U : Set ℂ} (hU : IsOpen U)
    {Ω : ℂ × ℂ → (ℂ × ℂ) [⋀^Fin 2]→L[ℝ] ℝ}
    (hΩ : ContDiffOn ℝ ∞ Ω (U ×ˢ ClosedDiscTraceDomain))
    (hclosed : ∀ p ∈ U ×ˢ Metric.ball (0 : ℂ) 1, extDeriv Ω p = 0)
    (hJ : ∀ p ∈ U ×ˢ Metric.ball (0 : ℂ) 1, ∀ u v : ℂ × ℂ,
      Ω p ![Complex.I • u, Complex.I • v] = Ω p ![u, v]) (h0 : (0 : ℂ) ∈ U) :
    mixedReal (fun z => ∫ ζ in Metric.ball (0 : ℂ) 1,
      Ω (z, ζ) ![((0, 1) : ℂ × ℂ), ((0, Complex.I) : ℂ × ℂ)]) =
      (1 / 4 : ℝ) * ∫ θ in (-Real.pi)..Real.pi,
        closedRealGradient (fun ζ => Ω (0, ζ)
          ![((1, 0) : ℂ × ℂ), ((Complex.I, 0) : ℂ × ℂ)])
          (Yau.Blueprint.circlePoint θ) (Yau.Blueprint.circlePoint θ) := by
  let A : ℂ × ℂ → ℝ := fun p => Ω p ![((0, 1) : ℂ × ℂ), ((0, Complex.I) : ℂ × ℂ)]
  let B : ℂ × ℂ → ℝ := fun p => Ω p ![((1, 0) : ℂ × ℂ), ((Complex.I, 0) : ℂ × ℂ)]
  have hA : ContDiffOn ℝ ∞ A (U ×ˢ ClosedDiscTraceDomain) :=
    twoFormCoefficient_contDiffOn hΩ (0, 1) (0, Complex.I)
  have hB : ContDiffOn ℝ ∞ B (U ×ˢ ClosedDiscTraceDomain) :=
    twoFormCoefficient_contDiffOn hΩ (1, 0) (Complex.I, 0)
  have hBslice : ContDiffOn ℝ ∞ (fun ζ => B (0, ζ)) ClosedDiscTraceDomain :=
    hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun ζ hζ => ⟨h0, hζ⟩)
  have hLap (ζ : ℂ) (hζ : ζ ∈ Metric.ball (0 : ℂ) 1) :
      discParameterDerivative (discParameterDerivative A U 1) U 1 (0, ζ) +
        discParameterDerivative (discParameterDerivative A U Complex.I) U Complex.I (0, ζ) =
          closedLaplacian (fun η => B (0, η)) ζ := by
    have hnhds : U ×ˢ ClosedDiscTraceDomain ∈ 𝓝 ((0, ζ) : ℂ × ℂ) :=
      mem_of_superset ((hU.prod Metric.isOpen_ball).mem_nhds ⟨h0, hζ⟩)
        (fun p hp => ⟨hp.1, Metric.ball_subset_closedBall hp.2⟩)
    have hAp : ContDiffAt ℝ 2 A (0, ζ) := (hA.contDiffAt hnhds).of_le (by simp)
    have hBp : ContDiffAt ℝ 2 B (0, ζ) := (hB.contDiffAt hnhds).of_le (by simp)
    have hh := closedJTwoForm_laplacian_exchange (hU.prod Metric.isOpen_ball)
      (hΩ.mono (fun p hp => ⟨hp.1, Metric.ball_subset_closedBall hp.2⟩)) hclosed hJ
      ((1, 0) : ℂ × ℂ) ((0, 1) : ℂ × ℂ) (p := (0, ζ)) ⟨h0, hζ⟩
    change fderivWithin ℝ (fun p => fderivWithin ℝ A (U ×ˢ ClosedDiscTraceDomain) p (1, 0))
        (U ×ˢ ClosedDiscTraceDomain) (0, ζ) (1, 0) +
      fderivWithin ℝ (fun p => fderivWithin ℝ A (U ×ˢ ClosedDiscTraceDomain) p (Complex.I, 0))
        (U ×ˢ ClosedDiscTraceDomain) (0, ζ) (Complex.I, 0) = _
    rw [secondWithin_directional_eq hnhds hAp, secondWithin_directional_eq hnhds hAp,
      closedLaplacian_eq hζ, secondFDeriv_spatial_slice hBp, secondFDeriv_spatial_slice hBp]
    simpa only [Prod.smul_mk, smul_eq_mul, mul_zero, mul_one] using hh
  have hD11 := discParameterDerivative_contDiffOn hU (discParameterDerivative_contDiffOn hU hA 1) 1
  have hDII := discParameterDerivative_contDiffOn hU
    (discParameterDerivative_contDiffOn hU hA Complex.I) Complex.I
  change mixedReal (fun z => ∫ ζ in Metric.ball (0 : ℂ) 1, A (z, ζ)) = _
  rw [mixedReal_discIntegral hU hA h0,
    ← integral_add (discDensity_slice_integrable hD11.continuousOn h0)
      (discDensity_slice_integrable hDII.continuousOn h0)]
  have heq : (∫ ζ in Metric.ball (0 : ℂ) 1,
      discParameterDerivative (discParameterDerivative A U 1) U 1 (0, ζ) +
        discParameterDerivative (discParameterDerivative A U Complex.I) U Complex.I (0, ζ)) =
      ∫ ζ in Metric.ball (0 : ℂ) 1, closedLaplacian (fun η => B (0, η)) ζ :=
    setIntegral_congr_fun measurableSet_ball hLap
  rw [heq, integral_closedLaplacian_eq_boundary hBslice]

end Yau.Blueprint.V03Proof
