import Yau.Proofs.V03ActualEnergyDerivative

/-! Changing the lower test leaves the geometry, admissibility, energy,
symbols and the actual boundary energy estimate unchanged. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem variationSetup_update_test {d : VariationData X q} (hd : VariationSetup d)
    (φ : CotangentPoint X.manifold → ℝ → ℝ)
    (hφ : StrictEnvelopeContact {d with test := φ}) :
    VariationSetup {d with test := φ} := by
  rcases hd with ⟨hT, hTT, hflow, hexh, hG, hZ, hw, _, hQ, hρ, hρlim,
    hA, hAlim, hj⟩
  exact ⟨hT, hTT, hflow, hexh, hG, hZ, hw, hφ, hQ, hρ, hρlim, hA, hAlim, hj⟩

@[simp] theorem variationEnergy_update_test (d : VariationData X q)
    (φ : CotangentPoint X.manifold → ℝ → ℝ) (j : ℕ) (F : VariationDisc X) :
    variationEnergy {d with test := φ} j F = variationEnergy d j F := rfl

@[simp] theorem admissibleVariationDisc_update_test (d : VariationData X q)
    (φ : CotangentPoint X.manifold → ℝ → ℝ) (j : ℕ) (F : VariationDisc X) :
    AdmissibleVariationDisc {d with test := φ} j F ↔ AdmissibleVariationDisc d j F :=
  Iff.rfl

@[simp] theorem boundarySymbol_update_test (d : VariationData X q)
    (φ : CotangentPoint X.manifold → ℝ → ℝ) (j a : ℕ)
    (F : VariationDisc X) (E : ℂ → CotangentMatrix n) (ζ : ℂ) :
    boundarySymbol {d with test := φ} j a F E ζ = boundarySymbol d j a F E ζ := rfl

@[simp] theorem outerCenter_update_test (d : VariationData X q)
    (φ : CotangentPoint X.manifold → ℝ → ℝ) (j a : ℕ) (F : VariationDisc X) :
    outerCenter {d with test := φ} j a F = outerCenter d j a F := rfl

@[simp] theorem realizesFirstField_update_test (d : VariationData X q)
    (φ : CotangentPoint X.manifold → ℝ → ℝ) (j a : ℕ) (F : VariationDisc X)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (r : ℝ) :
    RealizesFirstField {d with test := φ} j a F E l h α fz r ↔
      RealizesFirstField d j a F E l h α fz r := Iff.rfl

/-- The original V03 coefficient is chosen before the new test. Its
quantifier order is preserved without any interior-compact parameter. -/
theorem energyCoefficient_before_test {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (φ : CotangentPoint X.manifold → ℝ → ℝ)
        (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
        (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
        (fz : ℂ → ℂ → CotangentPoint X.manifold) (r : ℝ),
        AdmissibleVariationDisc {d with test := φ} j F →
        NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
        (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
        RealizesFirstField {d with test := φ} j a F E l h α fz r →
        |V03Proof.mixedReal (fun z =>
          (variationEnergy {d with test := φ} j {F with f := fz z}).toReal)| ≤
          C * (1 + (variationEnergy d j F).toReal +
            (boundaryDSq (fun θ => l (circlePoint θ))).toReal) := by
  obtain ⟨C, hC, he⟩ := V03Proof.actualEnergyDerivative hd j a ha L hL
  exact ⟨C, hC, fun _ F E l h α fz r hF hE hl hbound hR =>
    he F E l h α fz r hF hE hl hbound hR⟩

end Yau.Blueprint.V02Proof
