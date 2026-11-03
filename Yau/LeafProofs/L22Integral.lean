import Yau.LeafProofs.L22Convex

noncomputable section

open scoped Topology ContDiff
open MeasureTheory Set

namespace Yau.LeafProofs.L22Aux

variable {n : ℕ}

theorem complexLinePshOn_translate {O V : Set (ComplexVector n)}
    {f : ComplexVector n → ℝ} (hf : LeafCandidates.ComplexLinePshOn O f)
    (a : ComplexVector n) (hVO : ∀ z ∈ V, z - a ∈ O) :
    LeafCandidates.ComplexLinePshOn V (fun z => f (z - a)) := by
  refine ⟨hf.1.comp (continuous_id.sub continuous_const).continuousOn hVO, ?_⟩
  intro z w hdisc
  have hdisc' : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → (z - a) + ζ • w ∈ O := by
    intro ζ hζ
    convert hVO _ (hdisc ζ hζ) using 1 <;> abel
  have h := hf.2 (z - a) w hdisc'
  convert h using 1
  congr 1
  funext θ
  congr 1
  abel

/-- Fubini for the frozen circle average, with the joint integrability
condition explicit. This is the order exchange used by local convolution. -/
theorem integral_circleAverage {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] {F : S → ℝ → ℝ}
    (hF : Integrable (Function.uncurry F)
      (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) :
    (∫ s, circleAverage (F s) ∂μ) = circleAverage (fun θ => ∫ s, F s θ ∂μ) := by
  simp only [circleAverage, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  rw [integral_const_mul, integral_integral_swap hF]

/-- An integrable family of genuine line-submean functions satisfies the
same submean inequality after integration. Smooth convolution supplies the
separate continuity premise in its application. -/
theorem complexLinePshOn_integral {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] {O : Set (ComplexVector n)}
    (F : S → ComplexVector n → ℝ)
    (hF : ∀ s, LeafCandidates.ComplexLinePshOn O (F s))
    (hc : ContinuousOn (fun z => ∫ s, F s z ∂μ) O)
    (hi : ∀ z ∈ O, Integrable (fun s => F s z) μ)
    (hjoint : ∀ z w : ComplexVector n,
      (∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ O) →
      Integrable (fun p : S × ℝ => F p.1 (z + Complex.exp (p.2 * Complex.I) • w))
        (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) :
    LeafCandidates.ComplexLinePshOn O (fun z => ∫ s, F s z ∂μ) := by
  refine ⟨hc, ?_⟩
  intro z w hdisc
  have hz : z ∈ O := by simpa using hdisc 0 (by simp)
  have hprod := hjoint z w hdisc
  have hmean : Integrable
      (fun s => circleAverage (fun θ => F s (z + Complex.exp (θ * Complex.I) • w))) μ := by
    simpa only [circleAverage, intervalIntegral.integral_of_le
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using
      hprod.integral_prod_left.const_mul ((2 * Real.pi)⁻¹)
  calc
    (∫ s, F s z ∂μ) ≤
        ∫ s, circleAverage (fun θ => F s (z + Complex.exp (θ * Complex.I) • w)) ∂μ :=
      integral_mono (hi z hz) hmean (fun s => (hF s).2 z w hdisc)
    _ = _ := integral_circleAverage μ hprod

theorem complexLinePshOn_integral_ae {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] {O : Set (ComplexVector n)}
    (F : S → ComplexVector n → ℝ)
    (hF : ∀ᵐ s ∂μ, LeafCandidates.ComplexLinePshOn O (F s))
    (hc : ContinuousOn (fun z => ∫ s, F s z ∂μ) O)
    (hi : ∀ z ∈ O, Integrable (fun s => F s z) μ)
    (hjoint : ∀ z w : ComplexVector n,
      (∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ O) →
      Integrable (fun p : S × ℝ => F p.1 (z + Complex.exp (p.2 * Complex.I) • w))
        (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) :
    LeafCandidates.ComplexLinePshOn O (fun z => ∫ s, F s z ∂μ) := by
  refine ⟨hc, ?_⟩
  intro z w hdisc
  have hz : z ∈ O := by simpa using hdisc 0 (by simp)
  have hprod := hjoint z w hdisc
  have hmean : Integrable
      (fun s => circleAverage (fun θ => F s (z + Complex.exp (θ * Complex.I) • w))) μ := by
    simpa only [circleAverage, intervalIntegral.integral_of_le
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using
      hprod.integral_prod_left.const_mul ((2 * Real.pi)⁻¹)
  calc
    (∫ s, F s z ∂μ) ≤
        ∫ s, circleAverage (fun θ => F s (z + Complex.exp (θ * Complex.I) • w)) ∂μ :=
      integral_mono_ae (hi z hz) hmean (hF.mono fun s hs => hs.2 z w hdisc)
    _ = _ := integral_circleAverage μ hprod

end Yau.LeafProofs.L22Aux
