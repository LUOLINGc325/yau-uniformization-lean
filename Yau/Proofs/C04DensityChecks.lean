import Yau.Proofs.C04ClockChecks
import Yau.Proofs.C04SpatialDensity

/-! Literal checks of the complete clock and compact-density portion of original C04. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint BlueprintContracts

theorem clock_and_density_of_originalC01 (hC01 : C01_contract) :
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
      |ρ x t / s t - 1| ≤ ε) := by
  intro n X o h U P ρ hf
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := clock_clauses_of_originalC01 hC01 n X o h U P ρ hf
  exact ⟨h₁, h₂, h₃, h₄, h₅, compact_rho_ratio X o h U P ρ hf
    (hC01 n X o h U P ρ hf)⟩

example (hC01 : C01_contract) (X : KahlerManifold 0) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ) :
    ∀ K : Set (Pt X), IsCompact K → ∀ ε, 0 < ε → ∃ T, ∀ t, T ≤ t → ∀ x ∈ K,
      |ρ x t / ρ o t - 1| ≤ ε :=
  (clock_and_density_of_originalC01 hC01 0 X o h U P ρ hf).2.2.2.2.2

end Yau.Proofs.C04Aux
