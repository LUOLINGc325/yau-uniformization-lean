import spec.CHAIN.CONTRACTS

/-! Numerical transfer along an already selected subsequence. Every weight
is chosen after the same sequence and its two value limits; no additional
subsequence is selected for any smooth weight. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem inverse_square_cap_tendsto_zero
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) (a : ℝ) :
    Tendsto (fun m => a / L m ^ 2) atTop (𝓝 0) := by
  have hh : Tendsto (fun m => a * (L m)⁻¹ ^ 2) atTop (𝓝 (a * 0 ^ 2)) :=
    tendsto_const_nhds.mul ((tendsto_inv_atTop_zero.comp hL).pow 2)
  simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, div_eq_mul_inv, inv_pow] using
    (hh : Tendsto (fun m => a * (L m)⁻¹ ^ 2) atTop (𝓝 (a * 0 ^ 2)))

theorem nonpositive_of_eventual_inverse_square_cap
    {L f : ℕ → ℝ} {a v : ℝ}
    (hL : Tendsto L atTop atTop) (hf : Tendsto f atTop (𝓝 v))
    (hcap : ∀ᶠ m in atTop, f m ≤ a / L m ^ 2) : v ≤ 0 := by
  have hh : Tendsto (fun m => f m - a / L m ^ 2) atTop (𝓝 v) := by
    simpa only [sub_zero] using hf.sub (inverse_square_cap_tendsto_zero hL a)
  exact le_of_tendsto hh (hcap.mono (fun _ h => sub_nonpos.mpr h))

theorem same_sequence_weight_comparison_limit
    (X : KahlerManifold n) (u : Pt X → ℝ)
    (Us Ps : ℕ → STF X) (U P : STF X) (σ : ℕ → ℕ)
    (hσ : StrictMono σ)
    (hU : ∀ x t, 0 ≤ t → Tendsto (fun m => Us (σ m) x t) atTop (𝓝 (U x t)))
    (hP : ∀ x t, 0 ≤ t → Tendsto (fun m => Ps (σ m) x t) atTop (𝓝 (P x t)))
    (η : ℝ)
    (hfinite : ∀ D : ℝ, 0 < D → ∀ ψ : Pt X → ℝ, SmoothFn ψ →
      (∀ x, HermLE (ricci X.metric.form x) (levi ψ x)) →
      ∀ ε : ℝ, 0 < ε → ε ≤ η / (D + 1) →
      ∀ A : ℝ, (∀ x, ψ x - ε * u x ^ 2 - A ≤ 0) →
      ∀ x t, t ∈ Icc 0 (D / 2) → ∀ᶠ m in atTop,
        0 ≤ (D - t) * Ps m x t + Us m x t -
          D * (ψ x - ε * u x ^ 2 - A) + (n : ℝ) * t) :
    ∀ D : ℝ, 0 < D → ∀ ψ : Pt X → ℝ, SmoothFn ψ →
      (∀ x, HermLE (ricci X.metric.form x) (levi ψ x)) →
      ∀ ε : ℝ, 0 < ε → ε ≤ η / (D + 1) →
      ∀ A : ℝ, (∀ x, ψ x - ε * u x ^ 2 - A ≤ 0) →
      ∀ x t, t ∈ Icc 0 (D / 2) →
        0 ≤ (D - t) * P x t + U x t -
          D * (ψ x - ε * u x ^ 2 - A) + (n : ℝ) * t := by
  intro D hD ψ hψ hRic ε hε hεη A hsign x t ht
  have hlim : Tendsto (fun m => (D - t) * Ps (σ m) x t + Us (σ m) x t -
      D * (ψ x - ε * u x ^ 2 - A) + (n : ℝ) * t) atTop
      (𝓝 ((D - t) * P x t + U x t -
        D * (ψ x - ε * u x ^ 2 - A) + (n : ℝ) * t)) :=
    (((tendsto_const_nhds.mul (hP x t ht.1)).add (hU x t ht.1)).sub
      tendsto_const_nhds).add tendsto_const_nhds
  exact ge_of_tendsto hlim
    (hσ.tendsto_atTop.eventually (hfinite D hD ψ hψ hRic ε hε hεη A hsign x t ht))

end Yau.NodeProofs.F01Aux
