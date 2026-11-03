import Yau.Proofs.Y03JumpOrder
import Yau.Proofs.Y03OrderedRates

/-! Joint Levi positivity gives the complete original RateOrder on every actual step. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ} {X : KahlerManifold n}

theorem rateOrder_of_jointPositiveClock {o : Pt X} {h : Flow X} {U P₀ ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hflow : FlowStage X o h U P₀ ρ) (hjoint : JointPositiveClock X h)
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E)
    (hlate : ∀ k, t₀ ≤ tk k) : RateOrder F tk E := by
  have hquad := actual_covector_rate_order hflow hjoint hCharts hE hlate
  refine ⟨hquad, ?_⟩
  intro i
  apply monotone_nat_of_le_succ
  intro k
  exact ordered_rates_le_of_unitary_order (jump_unitary hE k)
    (rate_monotone_index hE k) (rate_monotone_index hE (k + 1)) (hquad k) i

end Yau.Blueprint.Alignment.Y03Proof
