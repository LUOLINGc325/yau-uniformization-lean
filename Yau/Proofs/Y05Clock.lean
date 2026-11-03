import Yau.Proofs.Y05Jacobian

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint Filter
open scoped Topology

variable {n : ℕ}

/-- Divergence of the given clock forces divergence of the actual time grid.
This uses the center contraction and determinant identity, so it also covers
the unrestricted early times in the frozen contract. -/
theorem shrinking_clock_time_tendsto {X : KahlerManifold n}
    {o : Pt X} {h : Flow X} {ρ : STF X} {r₀ r₁ σ C Cb t₀ : ℝ}
    {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n}
    (hc : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk : ℕ → ℝ} (htk : StrictMono tk) (hlate : ∀ k, t₀ ≤ tk k)
    (hs : Tendsto (fun k => ρ o (tk k)) atTop atTop) : Tendsto tk atTop atTop := by
  apply htk.monotone.tendsto_atTop_atTop
  intro B
  by_contra hB
  push_neg at hB
  let T := max t₀ B
  let N : ℝ := Fintype.card (Equiv.Perm (Fin n))
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hs.eventually (eventually_ge_atTop
    (ρ o T + 2 * (N + 1))))
  have hclock := hK K le_rfl
  have hKT : tk K ≤ T := (hB K).le.trans (le_max_right _ _)
  have H := hc.2.2.2.2.2.1 (tk K) T (hlate K) hKT
  have hA : ‖fderiv ℂ (F (tk K) T) 0‖ ≤ 1 := H.2.2.2.2.1
  have hd : ‖LinearMap.det (fderiv ℂ (F (tk K) T) 0).toLinearMap‖ ≤ N := by
    apply (norm_linearMap_det_le _).trans
    change N * _ ≤ N
    have hp : ‖fderiv ℂ (F (tk K) T) 0‖ ^ n ≤ 1 :=
      (pow_le_pow_left₀ (norm_nonneg _) hA n).trans_eq (one_pow n)
    nlinarith [show 0 ≤ N by exact Nat.cast_nonneg _]
  rw [H.2.2.2.2.2.1] at hd
  have he := Real.add_one_le_exp (-(ρ o T - ρ o (tk K)) / 2)
  linarith

end Yau.Proofs.Y05Aux
