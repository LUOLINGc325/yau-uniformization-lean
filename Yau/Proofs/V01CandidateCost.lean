import Yau.Proofs.V01CandidateMajorant
import Yau.Proofs.V01SmoothedCost
import Yau.Proofs.V01ClockMajorant

/-! The actual candidate obeys the signed physical-clock estimate. -/

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder
namespace Yau.Blueprint.V01Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem candidateMajorant_cost_bound
    {d : VariationData X q} {k : ClockData X} {a j : ℕ} {δ r τ e e₁ e₂ e₃ β : ℝ}
    (hSub : SymplecticSubmean d k a) (hδ : 0 < δ)
    {F : VariationDisc X} {E H Hinv : ℂ → CotangentMatrix n}
    (hF : AdmissibleVariationDisc d j F) (hE : NormalizedDiscFrame d.G F.f E)
    (hSpec : SpectralFactorFor d j a δ F E H Hinv) (hr : 0 ≤ r) (hβ : 0 < β)
    (hReplacement : |clockSymplecticCost d k j a F -
      smoothedBoundaryCost d k j a δ F E| ≤ e₁)
    (hClock : clockSymplecticCost d k j a F ≤ clockBoundaryCost d k j a F + e₂)
    (hBoundary : clockBoundaryCost d k j a F ≤ τ + e + e₃)
    (hFactor : (1 + r) ^ 2 *
      Real.exp (-circleAverage (fun θ => Real.log (clockWeight d k j a F θ))) ≤ 2)
    (hFactorLoss : |(1 + r) ^ 2 *
      Real.exp (-circleAverage (fun θ => Real.log (clockWeight d k j a F θ))) - 1| *
        (1 + |τ|) ≤ β / 4)
    (hError : e + e₁ + e₂ + e₃ ≤ β / 4) :
    symplecticP (candidateMajorant d j a r F E H) ≤ τ + β := by
  have hChart := (admissible_center_in_chart hF).1
  have hS := frameInChart_isUnit d.chart F.f E 0 hChart (hE.1.1 0 (by simp))
  have hSm := spectral_submean_smoothed hSub hδ hF hE hSpec
  rw [← fixed_frameBivector d.chart F.f E 0 hChart] at hSm
  exact fixed_majorant_from_clock_small_errors (spectralFactor_center_isUnit hSpec)
    hS hr (outerCenter_pos d j a F) hβ hSm hReplacement hClock hBoundary
    hFactor hFactorLoss hError

end Yau.Blueprint.V01Proof
