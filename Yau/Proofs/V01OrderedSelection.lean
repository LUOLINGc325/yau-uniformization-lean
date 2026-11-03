import spec.CHAIN.CONTRACTS

/-! V01 scratch source. The witnesses are selected in the original order:
`j`, then positive `δ`, then positive `ε`, then the sequence term `ν`. -/

noncomputable section
open Set Filter
open scoped Topology

namespace Yau.Blueprint.V01Proof

theorem ordered_pick
    {P : ℕ → ℝ → ℝ → ℕ → Prop}
    (hP : ∀ᶠ j in atTop, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop, P j δ ε ν)
    (m : ℕ) (rδ rε : ℝ) (hrδ : 0 < rδ) (hrε : 0 < rε) :
    ∃ j δ ε ν, m ≤ j ∧ 0 < δ ∧ δ < rδ ∧ 0 < ε ∧ ε < rε ∧
      m ≤ ν ∧ P j δ ε ν := by
  obtain ⟨j, hj, hPj⟩ := ((eventually_ge_atTop m).and hP).exists
  obtain ⟨δ, hPδ, hδ⟩ := (hPj.and (Ioo_mem_nhdsGT hrδ)).exists
  obtain ⟨ε, hPε, hε⟩ := (hPδ.and (Ioo_mem_nhdsGT hrε)).exists
  obtain ⟨ν, hν, hPν⟩ := ((eventually_ge_atTop m).and hPε).exists
  exact ⟨j, δ, ε, ν, hj, hδ.1, hδ.2, hε.1, hε.2, hν, hPν⟩

theorem ordered_diagonal
    {P : ℕ → ℕ → ℝ → ℝ → ℕ → Prop}
    (hP : ∀ m, ∀ᶠ j in atTop, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop, P m j δ ε ν) :
    ∃ (j : ℕ → ℕ) (δ ε : ℕ → ℝ) (ν : ℕ → ℕ),
      ∀ m, m ≤ j m ∧ 0 < δ m ∧ δ m < ((m : ℝ) + 1)⁻¹ ∧
        0 < ε m ∧ ε m < ((m : ℝ) + 1)⁻¹ ∧ m ≤ ν m ∧
        P m (j m) (δ m) (ε m) (ν m) := by
  classical
  have hchoice (m : ℕ) := ordered_pick (hP m) m
    (((m : ℝ) + 1)⁻¹) (((m : ℝ) + 1)⁻¹) (by positivity) (by positivity)
  choose j δ ε ν h using hchoice
  exact ⟨j, δ, ε, ν, h⟩

end Yau.Blueprint.V01Proof
