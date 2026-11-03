import Yau.Proofs.C04ClockBasic
import Yau.Proofs.C04Positivity
import Yau.Proofs.C04ClockAnalysis

/-! The first five clauses of the original Ricci-window conclusion. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ}

theorem rho_strictMonoOn (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) {A : ℝ} (hA : 0 < A) :
    StrictMonoOn (ρ o) (Set.Ici A) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici A)
  · intro t ht
    exact (rho_hasDerivAt X o h U P ρ hf o (hA.trans_le ht)).continuousAt.continuousWithinAt
  · intro t ht
    exact (rho_hasDerivAt X o h U P ρ hf o
      (hA.trans_le (interior_subset ht))).hasDerivWithinAt
  · intro t ht
    exact scalar_pos X o h hH (hA.le.trans (interior_subset ht)) o

theorem clockSpeed_positive_lower (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) :
    ∃ c, 0 < c ∧ ∀ t, 1 ≤ t → c ≤ clockSpeed o h t := by
  refine ⟨clockSpeed o h 1, ?_, ?_⟩
  · simpa only [clockSpeed, one_mul] using scalar_pos X o h hH zero_le_one o
  · intro t ht
    have hm : MonotoneOn (clockSpeed o h) (Set.Ici (1 : ℝ)) :=
      clockSpeed_monotoneOn X o h U P ρ hf hH zero_lt_one
    exact hm (by simp) ht ht

theorem rho_tendsto_atTop (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) : Tendsto (ρ o) atTop atTop := by
  obtain ⟨c, hc, hb⟩ := clockSpeed_positive_lower X o h U P ρ hf hH
  exact tendsto_clock_of_speed_lower zero_lt_one hc
    (fun t ht => rho_hasDerivAt X o h U P ρ hf o (zero_lt_one.trans_le ht)) hb

theorem clockSpeed_liminf_bound (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) :
    ∀ ε, 0 < ε → ∀ T, ∃ t, T ≤ t ∧ clockSpeed o h t ≤ (2 + ε) * ρ o t := by
  intro ε hε T
  have hupper : ∃ C : ℝ, ∀ t, 0 ≤ t → ρ o t ≤ C * (1 + t) :=
    hf.2.2.2.2.2.2.2.2.2.2.2.2.1 o
  obtain ⟨t, ht, hb⟩ := exists_speed_le_twice_clock
    (fun t ht => rho_hasDerivAt X o h U P ρ hf o ht)
    (rho_tendsto_atTop X o h U P ρ hf hH) hupper (max T 0)
  refine ⟨t, (le_max_left T 0).trans ht, hb.trans ?_⟩
  have hrho : 0 ≤ ρ o t :=
    (hf.2.2.2.2.2.2.2.2.2.1 o t ((le_max_right T 0).trans ht)).2
  nlinarith

end Yau.Proofs.C04Aux
