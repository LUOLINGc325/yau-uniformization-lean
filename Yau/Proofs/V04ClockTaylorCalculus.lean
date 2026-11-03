import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Left-hand Taylor bounds and the sequence-before-increment limit. -/
open Filter Set
open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof.ClockTaylorAux

theorem backward_taylor_bound {f f₁ f₂ : ℝ → ℝ} {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Icc (-r) 0, HasDerivWithinAt f (f₁ x) (Icc (-r) 0) x)
    (hf₁ : ∀ x ∈ Icc (-r) 0, HasDerivWithinAt f₁ (f₂ x) (Icc (-r) 0) x)
    (hbound : ∀ x ∈ Icc (-r) 0, |f₂ x| ≤ M)
    {u : ℝ} (hu : u ∈ Icc (-r) 0) :
    |f u - f 0 - u * f₁ 0| ≤ M * u ^ 2 := by
  have hz : (0 : ℝ) ∈ Icc (-r) 0 := ⟨by linarith, le_rfl⟩
  have hD (x : ℝ) (hx : x ∈ Icc (-r) 0) : |f₁ x - f₁ 0| ≤ M * |x| := by
    simpa only [Real.norm_eq_abs, sub_zero] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf₁
        (fun y hy => by simpa only [Real.norm_eq_abs] using hbound y hy)
        (convex_Icc (-r) 0) hz hx
  let g : ℝ → ℝ := fun x => f x - f 0 - x * f₁ 0
  have hsub : Icc u 0 ⊆ Icc (-r) 0 := Icc_subset_Icc hu.1 le_rfl
  have hg (x : ℝ) (hx : x ∈ Icc u 0) :
      HasDerivWithinAt g (f₁ x - f₁ 0) (Icc u 0) x := by
    simpa only [g, Pi.sub_def, id_eq, sub_zero, one_mul] using
      (((hf x (hsub hx)).sub_const (f 0)).sub
        ((hasDerivAt_id x).hasDerivWithinAt.mul_const (f₁ 0))).mono hsub
  have hgb (x : ℝ) (hx : x ∈ Icc u 0) : |f₁ x - f₁ 0| ≤ M * |u| := by
    have hm : |x| ≤ |u| := by rw [abs_of_nonpos hx.2, abs_of_nonpos hu.2]; linarith [hx.1]
    exact (hD x (hsub hx)).trans (mul_le_mul_of_nonneg_left hm hM)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg
    (fun x hx => by simpa only [Real.norm_eq_abs] using hgb x hx)
    (convex_Icc u 0) (right_mem_Icc.mpr hu.2) (left_mem_Icc.mpr hu.2)
  have hh' : |f u - f 0 - u * f₁ 0| ≤ (M * |u|) * |u| := by
    simpa only [g, zero_mul, sub_self, sub_zero, Real.norm_eq_abs] using hh
  calc
    _ ≤ (M * |u|) * |u| := hh'
    _ = M * u ^ 2 := by rw [mul_assoc, ← pow_two, sq_abs]

theorem seqUpperZero_of_linear_quotients {a gap : ℕ → ℝ}
    (hgap : Tendsto gap atTop (𝓝 0))
    (hbound : ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      ∀ᶠ ν in atTop, a ν ≤ gap ν / ρ + C * ρ) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ ν in atTop, a ν ≤ τ := by
  obtain ⟨r, C, hr, hC, hb⟩ := hbound
  intro τ hτ
  let ρ : ℝ := min (r / 2) (τ / (4 * (C + 1)))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hsmall : C * ρ ≤ τ / 2 := by
    have hh := min_le_right (r / 2) (τ / (4 * (C + 1)))
    have hm : 4 * (C + 1) * ρ ≤ τ := by
      simpa only [ρ, mul_comm] using (le_div_iff₀ (by positivity : 0 < 4 * (C + 1))).mp hh
    nlinarith
  filter_upwards [hb ρ hρ hρr,
    hgap.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ρ * (τ / 2)))] with ν ha hg
  have hg' : gap ν / ρ ≤ τ / 2 := (div_le_iff₀ hρ).mpr (by linarith)
  linarith

theorem exp_clock_hasDerivAt (t γ u : ℝ) :
    HasDerivAt (fun v => t * Real.exp (v * γ))
      (t * γ * Real.exp (u * γ)) u := by
  convert (((hasDerivAt_id u).mul_const γ).exp.const_mul t) using 1 <;> simp [id_eq, pow_two, mul_comm, mul_left_comm, mul_assoc]

theorem exp_clock_second_hasDerivAt (t γ u : ℝ) :
    HasDerivAt (fun v => t * γ * Real.exp (v * γ))
      (t * γ ^ 2 * Real.exp (u * γ)) u := by
  convert (((hasDerivAt_id u).mul_const γ).exp.const_mul (t * γ)) using 1 <;> simp [id_eq, pow_two, mul_comm, mul_left_comm, mul_assoc]

end Yau.Blueprint.V04Proof.ClockTaylorAux
