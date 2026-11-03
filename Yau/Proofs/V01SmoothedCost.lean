import spec.CHAIN.CONTRACTS

/-! The boundary integral in positive replacement is exactly the integral
in the submean estimate for the chosen spectral factor. -/

noncomputable section
open scoped Topology Matrix
namespace Yau.Blueprint.V01Proof
variable {n q : ℕ} {X : KahlerManifold n}

def smoothedBoundaryCost (d : VariationData X q) (k : ClockData X) (j a : ℕ)
    (δ : ℝ) (F : VariationDisc X) (E : ℂ → CotangentMatrix n) : ℝ :=
  circleAverage (fun θ => discTime F (circlePoint θ) / F.s * clockWeight d k j a F θ *
    (wallPower d j a (F.f (circlePoint θ)) ^ 4)⁻¹ *
    bivectorCost (smoothMajorant δ (boundarySymbol d j a F E (circlePoint θ)))
      (frameBivector (E (circlePoint θ))))

theorem spectral_boundaryCost_eq
    {d : VariationData X q} (k : ClockData X) {j a : ℕ} {δ : ℝ}
    {F : VariationDisc X} {E H Hinv : ℂ → CotangentMatrix n}
    (hSpec : SpectralFactorFor d j a δ F E H Hinv) :
    circleAverage (fun θ => discTime F (circlePoint θ) / F.s * clockWeight d k j a F θ *
      (wallPower d j a (F.f (circlePoint θ)) ^ 4)⁻¹ *
      bivectorCost ((H (circlePoint θ))ᴴ * H (circlePoint θ))
        (frameBivector (E (circlePoint θ)))) = smoothedBoundaryCost d k j a δ F E := by
  unfold smoothedBoundaryCost
  apply congrArg circleAverage
  funext θ
  rw [hSpec.2.2 θ]

theorem spectral_submean_smoothed
    {d : VariationData X q} {k : ClockData X} {a : ℕ}
    (hSub : SymplecticSubmean d k a)
    {j : ℕ} {δ : ℝ} (hδ : 0 < δ) {F : VariationDisc X}
    {E H Hinv : ℂ → CotangentMatrix n}
    (hF : AdmissibleVariationDisc d j F) (hE : NormalizedDiscFrame d.G F.f E)
    (hSpec : SpectralFactorFor d j a δ F E H Hinv) :
    Real.exp (circleAverage (fun θ => Real.log (clockWeight d k j a F θ))) *
      (outerCenter d j a F ^ 4)⁻¹ *
        bivectorCost ((H 0)ᴴ * H 0) (frameBivector (E 0)) ≤
      smoothedBoundaryCost d k j a δ F E := by
  have h := hSub j δ F E H Hinv hδ hF hE hSpec
  rwa [spectral_boundaryCost_eq k hSpec] at h

end Yau.Blueprint.V01Proof
