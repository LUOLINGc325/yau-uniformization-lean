import Mathlib

/-! Actual cofinal admissible times can be chosen so that their terminal
reflection reaches one fixed later cylinder. All reflection points remain
in the earlier supplied cylinder. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux

theorem F05_cofinal_reflection_times {E : Set ℝ} {T t₀ s : ℝ}
    (hs : s < t₀) (ht₀ : t₀ < T) (hNot : T ∉ E)
    (hNear : ∀ ε : ℝ, 0 < ε → ∃ t ∈ E, T-ε < t ∧ t ≤ T) :
    ∃ τ : ℕ → ℝ, Tendsto τ atTop (𝓝 T) ∧
      ∀ k, τ k ∈ E ∧ t₀ < τ k ∧ τ k < T ∧ 0 ≤ 3*(τ k-s)-2*(T-s) := by
  let δ := min ((T-t₀)/2) ((T-s)/6)
  have hδ : 0 < δ := by
    dsimp only [δ]
    apply lt_min <;> linarith
  have hε (k : ℕ) : 0 < min δ (1/((k:ℝ)+1)) :=
    lt_min hδ (by positivity)
  choose τ hMem hNearτ hLe using fun k : ℕ => hNear (min δ (1/((k:ℝ)+1))) (hε k)
  have hLower (k : ℕ) : T-1/((k:ℝ)+1) ≤ τ k := by
    have hh := hNearτ k
    have hm := min_le_right δ (1/((k:ℝ)+1))
    linarith
  have hConv : Tendsto τ atTop (𝓝 T) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using ((tendsto_const_nhds (x := T)).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 0))))
      tendsto_const_nhds hLower hLe
  refine ⟨τ,hConv,?_⟩
  intro k
  have hδ₁ : δ ≤ (T-t₀)/2 := min_le_left _ _
  have hδ₂ : δ ≤ (T-s)/6 := min_le_right _ _
  have hNearδ : T-δ < τ k := by
    have hh := hNearτ k
    have hm := min_le_left δ (1/((k:ℝ)+1))
    linarith
  refine ⟨hMem k,by linarith,lt_of_le_of_ne (hLe k) ?_,by linarith⟩
  intro hEq
  exact hNot (hEq ▸ hMem k)

end Yau.Proofs.F05Aux
