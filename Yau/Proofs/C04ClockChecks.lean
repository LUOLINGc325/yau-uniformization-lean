import Yau.Proofs.C04ClockInverse
import Yau.Proofs.C04GoodWindows
import spec.CHAIN.CONTRACTS

/-! Literal checks of the original clock clauses, including dimension zero. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint BlueprintContracts

/-- Exactly the first five clauses of the frozen C04 conclusion. The
remaining spatial and rescaled-flow clauses are not asserted here. -/
theorem clock_clauses_of_originalC01 (hC01 : C01_contract) :
    ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X),
    LocalizedFlow X o h U P ρ →
    (∃ t₁, 0 < t₁ ∧ StrictMonoOn (ρ o) (Set.Ici t₁) ∧
      MonotoneOn (clockSpeed o h) (Set.Ici t₁) ∧
      ∀ t, t₁ ≤ t → HasDerivAt (ρ o) (scalarCurvature (h t) o) t) ∧
    (∃ c, 0 < c ∧ ∃ t₂, ∀ t, t₂ ≤ t → c ≤ clockSpeed o h t) ∧
    Tendsto (ρ o) atTop atTop ∧
    (∃ C, ∀ t, 1 ≤ t → clockSpeed o h t ≤ C * t) ∧
    (∀ ε, 0 < ε → ∀ T, ∃ t, T ≤ t ∧ clockSpeed o h t ≤ (2 + ε) * ρ o t) := by
  intro n X o h U P ρ hf
  have hH : HarnackCompleteness X o h := hC01 n X o h U P ρ hf
  obtain ⟨c, hc, hcb⟩ := clockSpeed_positive_lower X o h U P ρ hf hH
  exact ⟨⟨1, zero_lt_one, rho_strictMonoOn X o h U P ρ hf hH zero_lt_one,
      clockSpeed_monotoneOn X o h U P ρ hf hH zero_lt_one,
      fun t ht => rho_hasDerivAt X o h U P ρ hf o (zero_lt_one.trans_le ht)⟩,
    ⟨c, hc, 1, hcb⟩, rho_tendsto_atTop X o h U P ρ hf hH,
    clockSpeed_linear_bound X o h hH, clockSpeed_liminf_bound X o h U P ρ hf hH⟩

example (hC01 : C01_contract) (n : ℕ) (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ) :
    ∀ ε, 0 < ε → ∀ T, ∃ t, T ≤ t ∧ clockSpeed o h t ≤ (2 + ε) * ρ o t :=
  (clock_clauses_of_originalC01 hC01 n X o h U P ρ hf).2.2.2.2

example (hC01 : C01_contract) (X : KahlerManifold 0) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ) :
    Tendsto (ρ o) atTop atTop :=
  (clock_clauses_of_originalC01 hC01 0 X o h U P ρ hf).2.2.1

example (X : KahlerManifold 0) (o : Pt X) (h : Flow X)
    (hH : HarnackCompleteness X o h) (t : ℝ) (ht : 0 ≤ t) :
    0 < scalarCurvature (h t) o := scalar_pos X o h hH ht o

end Yau.Proofs.C04Aux
