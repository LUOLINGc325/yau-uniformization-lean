import Yau.Proofs.V02AreaTaylorIntegral
import Yau.Proofs.V03VectorAreaFourier

/-! Genuine holomorphic Dirichlet data control the integrable first-disc
velocity weight. All ENNReal seminorms are converted only through finite bounds. -/

open scoped Topology ContDiff
open Filter MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof
open Yau Yau.Blueprint V03Proof

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem closedDerivative_sq_integrable {f : ℂ → H}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall 0 1)) :
    IntegrableOn (fun ζ => ‖closedDiscDerivative f ζ‖ ^ 2) (Metric.ball (0 : ℂ) 1) :=
  (((continuousOn_closedDiscDerivative hf).norm.pow 2).integrableOn_compact
    (μ := volume) (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall

theorem integral_closedDerivative_sq_eq_half_area {f : ℂ → H}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall 0 1)) :
    (∫ ζ in Metric.ball (0 : ℂ) 1, ‖closedDiscDerivative f ζ‖ ^ 2) =
      (normDiscArea f).toReal / 2 := by
  have heq : normDiscArea f = ENNReal.ofReal
      (∫ ζ in Metric.ball (0 : ℂ) 1, 2 * ‖closedDiscDerivative f ζ‖ ^ 2) := by
    simpa only [radialEuclideanDensity, Complex.ofReal_one, one_mul, one_smul] using
      (normDiscArea_radial_eq_integral hf (r := 1) (by simp))
  rw [heq, ENNReal.toReal_ofReal (integral_nonneg (fun ζ => by positivity)), integral_const_mul]
  ring

theorem integral_closedDerivative_sq_le_scalarDSq {h : ℂ → ℂ}
    (hh : ContDiffOn ℂ ∞ h (Metric.closedBall 0 1)) {H0 : ℝ} (hH0 : 0 ≤ H0)
    (hbound : boundaryDSq (fun θ (_ : Unit) => h (circlePoint θ)) ≤ ENNReal.ofReal H0) :
    (∫ ζ in Metric.ball (0 : ℂ) 1, ‖closedDiscDerivative h ζ‖ ^ 2) ≤ Real.pi * H0 := by
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_ofReal hH0] at hb
  rw [integral_closedDerivative_sq_eq_half_area hh, normDiscArea_scalar_eq_boundaryDSq hh,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)]
  nlinarith [Real.pi_pos]

theorem integral_closedDerivative_sq_le_vectorDSq {ι : Type*} [Fintype ι]
    {h : ℂ → EuclideanSpace ℂ ι} (hh : ContDiffOn ℂ ∞ h (Metric.closedBall 0 1))
    {H0 : ℝ} (hH0 : 0 ≤ H0)
    (hbound : boundaryDSq (fun θ i => h (circlePoint θ) i) ≤ ENNReal.ofReal H0) :
    (∫ ζ in Metric.ball (0 : ℂ) 1, ‖closedDiscDerivative h ζ‖ ^ 2) ≤ Real.pi * H0 := by
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_ofReal hH0] at hb
  rw [integral_closedDerivative_sq_eq_half_area hh, normDiscArea_vector_eq_boundaryDSq hh,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)]
  nlinarith [Real.pi_pos]

def inputDerivativeWeight {q b : ℕ} (X : ℂ → ComplexVector q) (h : ℂ → ℂ)
    (c : ℂ → ComplexVector b) (ζ : ℂ) : ℝ :=
  ‖closedDiscDerivative X ζ‖ ^ 2 + ‖closedDiscDerivative h ζ‖ ^ 2 + ‖closedDiscDerivative c ζ‖ ^ 2

theorem inputDerivativeWeight_integrable {q b : ℕ} {X : ℂ → ComplexVector q}
    {h : ℂ → ℂ} {c : ℂ → ComplexVector b}
    (hX : ContDiffOn ℂ ∞ X (Metric.closedBall 0 1))
    (hh : ContDiffOn ℂ ∞ h (Metric.closedBall 0 1))
    (hc : ContDiffOn ℂ ∞ c (Metric.closedBall 0 1)) :
    IntegrableOn (inputDerivativeWeight X h c) (Metric.ball (0 : ℂ) 1) :=
  ((closedDerivative_sq_integrable hX).add (closedDerivative_sq_integrable hh)).add
    (closedDerivative_sq_integrable hc)

theorem integral_inputDerivativeWeight_le {q b : ℕ} {X : ℂ → ComplexVector q}
    {h : ℂ → ℂ} {c : ℂ → ComplexVector b}
    (hX : ContDiffOn ℂ ∞ X (Metric.closedBall 0 1))
    (hh : ContDiffOn ℂ ∞ h (Metric.closedBall 0 1))
    (hc : ContDiffOn ℂ ∞ c (Metric.closedBall 0 1))
    {E0 H0 D0 : ℝ} (hH0 : 0 ≤ H0) (hD0 : 0 ≤ D0)
    (hE : (euclideanArea X).toReal ≤ E0)
    (hH : boundaryDSq (fun θ (_ : Unit) => h (circlePoint θ)) ≤ ENNReal.ofReal H0)
    (hD : boundaryDSq (fun θ k => c (circlePoint θ) k) ≤ ENNReal.ofReal D0) :
    (∫ ζ in Metric.ball (0 : ℂ) 1, inputDerivativeWeight X h c ζ) ≤
      E0 / 2 + Real.pi * H0 + Real.pi * D0 := by
  change (∫ ζ in Metric.ball (0 : ℂ) 1,
    (‖closedDiscDerivative X ζ‖ ^ 2 + ‖closedDiscDerivative h ζ‖ ^ 2) +
      ‖closedDiscDerivative c ζ‖ ^ 2) ≤ _
  rw [integral_add (μ := volume.restrict (Metric.ball (0 : ℂ) 1)) (f := fun ζ => ‖closedDiscDerivative X ζ‖ ^ 2 + ‖closedDiscDerivative h ζ‖ ^ 2)
    (by simpa only [IntegrableOn, Pi.add_def] using
      (closedDerivative_sq_integrable hX).add (closedDerivative_sq_integrable hh))
    (closedDerivative_sq_integrable hc),
    integral_add (closedDerivative_sq_integrable hX) (closedDerivative_sq_integrable hh),
    integral_closedDerivative_sq_eq_half_area hX]
  have hhB := integral_closedDerivative_sq_le_scalarDSq hh hH0 hH
  have hcB := integral_closedDerivative_sq_le_vectorDSq hc hD0 hD
  change (normDiscArea X).toReal ≤ E0 at hE
  linarith

end Yau.Blueprint.V02AreaTaylorProof
