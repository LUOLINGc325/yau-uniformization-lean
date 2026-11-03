import spec.WORKPACKAGES.«05-09».U02_SOURCE_SCOPE.DomainAdapter

/-! The actual physical and volume clocks of an original model. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint

/-- Arbitrary fixed chart thresholds are eventually passed by the original
physical times. This uses precisely U02's nonnegative-time gate. -/
theorem eventually_models_time_ge {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P ρ)
    (hp : PolynomialModels X o ρ F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) (T : ℝ) :
    ∀ᶠ k in atTop, T ≤ tk k :=
  (tendsto_atTop.1 (U02SourceScope.models_physical_time_cofinal hf hp ht)) T

/-- The volume clock grows past any fixed positive threshold. -/
theorem eventually_models_clock_ge {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {ρ : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o ρ F d hm Cd Dg tk H Hinv G Ginv) (S : ℝ) :
    ∀ᶠ k in atTop, S ≤ ρ o (tk k) :=
  (tendsto_atTop.1 hp.2.1) S

end Yau.NodeProofs.U02Proof
