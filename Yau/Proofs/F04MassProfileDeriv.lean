import Yau.Proofs.F04MassCutoff

open Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

theorem massProfile_scaled_deriv (R s : ℝ) :
    deriv (fun z => massProfile (z / R)) s = deriv massProfile (s / R) / R := by
  have hd := (massProfile_smooth.differentiable (by simp) (s / R)).hasDerivAt.comp s
    ((hasDerivAt_id s).div_const R)
  simpa only [Function.comp_def, id_eq, mul_one_div] using hd.deriv

theorem massProfile_scaled_secondDeriv (R s : ℝ) :
    deriv (deriv (fun z => massProfile (z / R))) s = deriv (deriv massProfile) (s / R) / R ^ 2 := by
  have hd : Differentiable ℝ (deriv massProfile) :=
    (contDiff_infty_iff_deriv.mp massProfile_smooth).2.differentiable (by simp)
  have heq : deriv (fun z => massProfile (z / R)) = fun z => deriv massProfile (z / R) / R :=
    funext (massProfile_scaled_deriv R)
  rw [heq]
  have hD := ((hd (s / R)).hasDerivAt.comp s ((hasDerivAt_id s).div_const R)).div_const R
  simpa only [Function.comp_def, id_eq, mul_one_div, div_div, ← pow_two] using hD.deriv

theorem massProfile_flat_off {s : ℝ} (hs : s < 1 ∨ 2 < s) :
    deriv massProfile s = 0 ∧ deriv (deriv massProfile) s = 0 := by
  rcases hs with hs | hs
  · have hh := massProfile_one_germ hs
    constructor
    · simpa only [deriv_const] using hh.deriv_eq
    · simpa only [deriv_const', deriv_const] using hh.deriv.deriv_eq
  · have hh := massProfile_zero_germ hs
    constructor
    · simpa only [deriv_const] using hh.deriv_eq
    · simpa only [deriv_const', deriv_const] using hh.deriv.deriv_eq

theorem massProfile_scaled_bounds : ∃ B : ℝ, 0 < B ∧ ∀ R : ℝ, 0 < R → ∀ s : ℝ,
    |deriv (fun z => massProfile (z / R)) s| ≤ B / R ∧
      |deriv (deriv (fun z => massProfile (z / R))) s| ≤ B / R ^ 2 := by
  obtain ⟨B, hB, hder⟩ := massProfile_derivative_bounds
  refine ⟨B, hB, ?_⟩
  intro R hR s
  rw [massProfile_scaled_deriv, massProfile_scaled_secondDeriv,
    abs_div, abs_div, abs_of_pos hR, abs_of_pos (sq_pos_of_pos hR)]
  exact ⟨div_le_div_of_nonneg_right (hder _).1 hR.le,
    div_le_div_of_nonneg_right (hder _).2 (sq_nonneg _)⟩

theorem massProfile_scaled_flat {R s : ℝ} (hR : 0 < R) (hs : s < R ∨ 2 * R < s) :
    deriv (fun z => massProfile (z / R)) s = 0 ∧
      deriv (deriv (fun z => massProfile (z / R))) s = 0 := by
  have hratio : s / R < 1 ∨ 2 < s / R := by
    rcases hs with hs | hs
    · exact Or.inl ((div_lt_one hR).mpr hs)
    · exact Or.inr ((lt_div_iff₀ hR).mpr hs)
  have hh := massProfile_flat_off hratio
  rw [massProfile_scaled_deriv, massProfile_scaled_secondDeriv, hh.1, hh.2, zero_div, zero_div]
  exact ⟨rfl, rfl⟩

end Yau.F04Proof
