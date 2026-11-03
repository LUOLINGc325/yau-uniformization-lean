import Yau.Proofs.V01CandidateCost
import Yau.Proofs.V01ClockTolerance
import Yau.Proofs.V01PositiveParameter
import Yau.Proofs.V01SpectralChoice

/-! The complete inner estimate follows the order j, then δ, then ε,
then the minimizing sequence. The master discs and frames precede δ. -/

noncomputable section
open Set Filter
open scoped Topology Matrix ComplexOrder MatrixOrder
namespace Yau.Blueprint.V01Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem localized_positive_majorants
    (d : VariationData X q) (k : ClockData X) (a : ℕ)
    (hContact : StrictEnvelopeContact d) (hLoc : LocalizationEstimates d)
    (hCenter : CenterMajorants d a) (hNegative : NegativePartEstimates d a)
    (hSpec : SpectralFactorEstimates d a) (hClock : ClockEstimates d k a)
    (hReplacement : PositiveReplacement d k a) (hSub : SymplecticSubmean d k a)
    (F : ℕ → ℝ → ℕ → VariationDisc X)
    (E : ℕ → ℝ → ℕ → ℂ → CotangentMatrix n)
    (hMin : LocalizedMinimizers d F)
    (hFrames : ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      MinimizingSequence d j ε (F j ε) ∧
        ∀ ν, NormalizedDiscFrame d.G (F j ε ν).f (E j ε ν))
    (τ : ℝ)
    (hTime : LocalizedZero (fun j ε ν =>
      deriv (d.test ((F j ε ν).f 0)) (F j ε ν).s - τ))
    (β : ℝ) (hβ : 0 < β) :
    ∀ᶠ j in atTop, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop,
        ∃ A : CotangentMatrix n, A.PosDef ∧
          (A - leviMatrix
            (fun z => d.test (cotangentChartInv d.chart z) (F j ε ν).s)
            (cotangentChart d.chart ((F j ε ν).f 0)) cotangentDir).PosSemidef ∧
          symplecticP A ≤ τ + β := by
  obtain ⟨C, hC, hClockAll⟩ := hClock
  obtain ⟨_hRawLog, _hRawWeight, hLog, hClockUpper, hBoundary⟩ := hClockAll F hMin
  obtain ⟨tol, hTol, hFactor⟩ := exists_clock_factor_tolerance τ β hβ
  let r : ℝ := tol / 2
  have hr : 0 < r := half_pos hTol
  have hrTol : |r| ≤ tol := by rw [abs_of_pos hr]; dsimp [r]; linarith
  have hb32 : 0 < β / 32 := by positivity
  have hb16 : 0 < β / 16 := by positivity
  have hEnergy := (hLoc.2.2 F hMin).1
  filter_upwards [hFrames, hEnergy, hCenter, hNegative,
    hLog tol hTol, hTime (β / 32) hb32, hClockUpper (β / 16) hb16,
    hBoundary] with j hFramesj hEnergyj hCenterj hNegativej hLogj hTimej hClockj hBoundaryj
  have hNegj := (hNegativej (F j) (E j) hFramesj hEnergyj).2
  obtain ⟨D, _hD, hReplacej⟩ := hReplacement j
  filter_upwards [eventually_positive_small_product D (β / 32) hb32] with δ hδ
  obtain ⟨_Cs, H, Hinv, _hCs, hSpecAll⟩ :=
    exists_spectral_factors_for_master d a hSpec j δ hδ.1 (F j) (E j) hFramesj
  have hSpecMin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), MinimizingSequence d j ε (F j ε) ∧
      ∀ ν, NormalizedDiscFrame d.G (F j ε ν).f (E j ε ν) ∧
        SpectralFactorFor d j a δ (F j ε ν) (E j ε ν) (H ε ν) (Hinv ε ν) :=
    hSpecAll.mono (fun _ h => ⟨h.1, fun ν => ⟨(h.2 ν).1, (h.2 ν).2.1⟩⟩)
  have hCenterεδ := hCenterj δ hδ.1 (F j) (E j) H Hinv hSpecMin hEnergyj r hr
  have hReplaceεδ := hReplacej δ hδ.1 hδ.2.1 (F j) (E j) hFramesj hNegj
    (β / 32) hb32
  have hEnergyTol : 0 < (β / 32) / (C j + 1) := by
    exact div_pos hb32 (by linarith [hC j])
  filter_upwards [hSpecMin, hCenterεδ, hReplaceεδ, hLogj, hTimej,
    hClockj, hBoundaryj, hEnergyj ((β / 32) / (C j + 1)) hEnergyTol]
    with ε hSpecε hCenterε hReplaceε hLogε hTimeε hClockε hBoundaryε hEnergyε
  filter_upwards [hCenterε, hReplaceε, hLogε, hTimeε, hClockε,
    hBoundaryε (β / 32) hb32, hEnergyε]
    with ν hCenterν hReplaceν hLogν hTimeν hClockν hBoundaryν hEnergyν
  have hFν := hSpecε.1.1 ν
  have hEν := (hSpecε.2 ν).1
  have hSFν := (hSpecε.2 ν).2
  have hMajorant := candidateMajorant_properties hContact hFν hEν hSFν hr.le hCenterν
  refine ⟨candidateMajorant d j a r (F j ε ν) (E j ε ν) (H ε ν),
    hMajorant.1, hMajorant.2.1, ?_⟩
  have hCE : C j * ε * (1 + (variationEnergy d j (F j ε ν)).toReal) ≤ β / 32 := by
    simpa only [mul_assoc] using nonneg_coefficient_small_of_abs (hC j) hEnergyν
  have hBound : clockBoundaryCost d k j a (F j ε ν) ≤ τ + β / 8 + 0 := by
    have hTimeUpper := (abs_le.mp hTimeν).2
    linarith
  have hReplaceBound : |clockSymplecticCost d k j a (F j ε ν) -
      smoothedBoundaryCost d k j a δ (F j ε ν) (E j ε ν)| ≤ β / 16 := by
    exact hReplaceν.trans (by linarith [hδ.2.2])
  have hFactors := hFactor r
    (circleAverage (fun θ => Real.log (clockWeight d k j a (F j ε ν) θ))) hrTol hLogν
  exact candidateMajorant_cost_bound hSub hδ.1 hFν hEν hSFν hr.le hβ
    hReplaceBound hClockν hBound hFactors.2.1 hFactors.2.2 (by linarith)

end Yau.Blueprint.V01Proof
