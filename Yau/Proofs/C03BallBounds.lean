import Yau.Proofs.C03FieldEnvelope

/-! Bounds for the attained moving-ball maximum use the same original
function and the actual field distance. -/

noncomputable section

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem fieldBallMaximum_le (h : HermitianField M) (hh : MetricSmooth h)
    (hcompact : ∀ p R, IsCompact {x | inducedDistance h p x ≤ R})
    (ψ : M.Carrier → ℝ) (hψ : Continuous ψ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (B : ℝ) (hupper : ∀ x, ψ x ≤ B) (z : M.Carrier) :
    fieldBallMaximum h ψ ρ z ≤ B := by
  obtain ⟨y, _, hy, _⟩ := fieldBallMaximum_spec h hh hcompact ψ hψ ρ hρ z
  rw [← hy]
  exact hupper y

theorem fieldBallMaximum_nonneg_of_near (h : HermitianField M) (hh : MetricSmooth h)
    (hcompact : ∀ p R, IsCompact {x | inducedDistance h p x ≤ R})
    (ψ : M.Carrier → ℝ) (hψ : Continuous ψ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (o : M.Carrier) (ho : 0 ≤ ψ o) (z : M.Carrier)
    (hnear : inducedDistance h z o ≤ ρ) : 0 ≤ fieldBallMaximum h ψ ρ z := by
  obtain ⟨_, _, _, hmax⟩ := fieldBallMaximum_spec h hh hcompact ψ hψ ρ hρ z
  exact ho.trans (hmax o hnear)

end Yau.Proofs.C03Aux
