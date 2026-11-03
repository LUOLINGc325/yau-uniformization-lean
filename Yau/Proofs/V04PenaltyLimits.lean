import Yau.Blueprint.VariationContracts

/-! Eliminate the sequential deformation error before the positive penalty
tends to zero. The coefficient is fixed before both limits. -/

open Filter
open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

theorem eps_upper_of_seq_upper_penalty (b e : ℝ → ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (he : EpsSeqZero (fun ε ν => ε * (1 + e ε ν)))
    (hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      SeqUpperZero (fun ν => b ε ν - C * ε * (1 + e ε ν))) :
    ∀ r : ℝ, 0 < r → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop, b ε ν ≤ r := by
  intro r hr
  have hden : 0 < 2 * (C + 1) := by positivity
  filter_upwards [he (r / (2 * (C + 1))) (div_pos hr hden), hb] with ε hε hseq
  filter_upwards [hε, hseq (r / 2) (half_pos hr)] with ν heν hbν
  have hp : C * (ε * (1 + e ε ν)) ≤ C * (r / (2 * (C + 1))) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans heν) hC
  have hbound : C * (r / (2 * (C + 1))) ≤ r / 2 := by
    have hquot : 0 ≤ r / (2 * (C + 1)) := (div_pos hr hden).le
    have h := (le_div_iff₀ hden).1 (le_refl (r / (2 * (C + 1))))
    nlinarith
  nlinarith

end Yau.Blueprint.V04Proof
