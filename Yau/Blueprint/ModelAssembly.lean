import Yau.Blueprint.Alignment

/-! The local model producer is stated on the same canonical grid and same
regular-model data consumed by the degree argument. This is an obligation,
not a construction proof. Degree charging is not a hypothesis or conclusion here. -/
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter
noncomputable section
namespace Yau.Blueprint.Alignment
open Yau Yau.Blueprint
def CanonicalModelConstruction : Prop :=
  ∀ n d : ℕ, 2 ≤ d → ∃ (Cd : ℝ) (Dstar : ℕ), 0 < Cd ∧ 1 ≤ Dstar ∧
    ∀ (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
      (r₀ r₁ σ C Cb t₀ : ℝ) (Φ : ℝ → ComplexVector n → Pt X)
      (F : ℝ → ℝ → ComplexVector n → ComplexVector n) (f : ℝ → Pt X → ComplexVector n),
      FlowStage X o h U P ρ → RicciWindows X o h ρ → JointPositiveClock X h →
      ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f →
      ∃ (time : ℝ → ℝ) (s₀ a₀ b₀ : ℝ), ClockParameter X o h ρ time s₀ ∧
        0 < a₀ ∧ a₀ < 1 ∧ 0 < b₀ ∧ ClockRateInput o h time s₀ a₀ b₀ ∧
        ∀ hm : ℝ, 0 < hm → hm < 1 → ∃ (N : ℕ) (M : ℝ),
          1 ≤ N ∧ Real.exp (-hm * N) ≤ a₀ ∧ 0 < M ∧
          Real.log (Dstar : ℝ) + max 0 (Real.log (2 / b₀)) / (2 * N + 1 : ℝ) ≤
            M / (3 * (2 * N + 1 : ℝ)) ∧ hm < M / (3 * (2 * N + 1 : ℝ)) ∧
          let Q := sampledSpeed o h time hm
          ∃ scale K eps b : ℝ, 0 < scale ∧ 0 < K ∧ 0 < eps ∧
            eps < 1 / (10 * (n + 1 : ℝ)) ∧ 0 < b ∧
            ∃ jLate : ℕ, N < jLate ∧
              ∀ j₀ : ℕ, jLate ≤ j₀ → Regular Q N M j₀ →
                let s := gridClock Q N M hm j₀
                let tk := fun k => time (s k)
                GridLayout Q N M hm j₀ ∧ (∀ k, s₀ ≤ s k ∧ t₀ ≤ tk k) ∧
                ∃ (H Hinv G Ginv g : ℕ → PolyMap n) (E : Frames n) (L : Changes n),
                  PolynomialModels X o ρ F d hm Cd Dstar tk H Hinv G Ginv ∧
                  WindowRateBounds Q N M hm b₀ j₀ (rate F tk E) ∧
                  WeightEstimates Q N M hm scale K eps b j₀ (rate F tk E) ∧
                  RegularModelCompatibility F tk Q N M hm scale K eps j₀ Dstar E L H G Ginv g

/-- Restricting the canonical macro subdivision is an exact index identity.
This is required before transferring a late infinite-run construction to an
arbitrary later regular start; no uniform-in-start bound is silently assumed. -/
def CanonicalGridTail : Prop :=
  ∀ (Q : ℕ → ℝ) (N : ℕ) (M hm : ℝ) (jBase j₀ : ℕ), jBase ≤ j₀ →
    GridLayout Q N M hm jBase → GridLayout Q N M hm j₀ →
    ∀ k, gridClock Q N M hm j₀ k =
      gridClock Q N M hm jBase (offset Q N M hm jBase j₀ + k)

end Yau.Blueprint.Alignment
