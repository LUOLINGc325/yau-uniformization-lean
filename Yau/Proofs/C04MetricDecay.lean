import Yau.Proofs.C04MetricLower
import Yau.Proofs.C04MetricUpper
import Yau.Proofs.C04DensityChecks

/-! The exact compact metric-decay clause, from the three original C04 parents. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint BlueprintContracts

variable {n : ℕ}

theorem compact_metric_decay (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (hCharts : UniformCharts X h) (hStatic : StaticDistortion X) :
    ∀ K : Set (Pt X), IsCompact K → ∃ cK, 0 < cK ∧ ∃ T, ∀ t, T ≤ t → ∀ x ∈ K,
      HermLE ((Real.exp (-2 * ρ o t) : ℂ) • gMat X.metric.form x) (gMat (h t) x) ∧
      HermLE (gMat (h t) x) ((Real.exp (-cK * ρ o t) : ℂ) • gMat X.metric.form x) := by
  intro K hK
  obtain ⟨Tl, hl⟩ := compact_metric_lower X o h U P ρ hf hH K hK
  obtain ⟨cK, hcK, Tu, hu⟩ := compact_metric_upper X o h U P ρ hf hH hCharts hStatic K hK
  exact ⟨cK, hcK, max Tl Tu, fun t ht x hx =>
    ⟨hl t ((le_max_left _ _).trans ht) x hx, hu t ((le_max_right _ _).trans ht) x hx⟩⟩

theorem first_seven_of_originalC01_C02_C03
    (hC01 : C01_contract) (hC02 : C02_contract) (hC03 : C03_contract) :
    ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X),
    LocalizedFlow X o h U P ρ →
    let s := fun t => ρ o t
    let q := clockSpeed o h
    (∃ t₁, 0 < t₁ ∧ StrictMonoOn s (Set.Ici t₁) ∧ MonotoneOn q (Set.Ici t₁) ∧
      ∀ t, t₁ ≤ t → HasDerivAt s (scalarCurvature (h t) o) t) ∧
    (∃ c, 0 < c ∧ ∃ t₂, ∀ t, t₂ ≤ t → c ≤ q t) ∧
    Tendsto s atTop atTop ∧
    (∃ C, ∀ t, 1 ≤ t → q t ≤ C * t) ∧
    (∀ ε, 0 < ε → ∀ T, ∃ t, T ≤ t ∧ q t ≤ (2 + ε) * s t) ∧
    (∀ K : Set (Pt X), IsCompact K → ∀ ε, 0 < ε → ∃ T, ∀ t, T ≤ t → ∀ x ∈ K,
      |ρ x t / s t - 1| ≤ ε) ∧
    (∀ K : Set (Pt X), IsCompact K → ∃ cK, 0 < cK ∧ ∃ T, ∀ t, T ≤ t → ∀ x ∈ K,
      HermLE ((Real.exp (-2 * s t) : ℂ) • gMat X.metric.form x) (gMat (h t) x) ∧
      HermLE (gMat (h t) x) ((Real.exp (-cK * s t) : ℂ) • gMat X.metric.form x)) := by
  intro n X o h U P ρ hf
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := clock_and_density_of_originalC01 hC01 n X o h U P ρ hf
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, compact_metric_decay X o h U P ρ hf
    (hC01 n X o h U P ρ hf) (hC02 n X o h U P ρ hf) (hC03 n X)⟩

example (hC01 : C01_contract) (hC02 : C02_contract) (hC03 : C03_contract)
    (X : KahlerManifold 0) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) :
    ∀ K : Set (Pt X), IsCompact K → ∃ cK, 0 < cK ∧ ∃ T, ∀ t, T ≤ t → ∀ x ∈ K,
      HermLE ((Real.exp (-2 * ρ o t) : ℂ) • gMat X.metric.form x) (gMat (h t) x) ∧
      HermLE (gMat (h t) x) ((Real.exp (-cK * ρ o t) : ℂ) • gMat X.metric.form x) :=
  (first_seven_of_originalC01_C02_C03 hC01 hC02 hC03 0 X o h U P ρ hf).2.2.2.2.2.2

end Yau.Proofs.C04Aux
