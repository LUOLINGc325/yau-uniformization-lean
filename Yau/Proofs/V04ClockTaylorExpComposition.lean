import Yau.Proofs.V04ClockTaylorCalculus

/-! A uniform Taylor estimate along the actual exponential physical-time
trajectory. The derivative data here are ordinary scalar calculus data. -/
open Set
noncomputable section
namespace Yau.Blueprint.V04Proof.ClockTaylorAux

theorem exp_composition_taylor {f f₁ f₂ : ℝ → ℝ} {r M t T γ C : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (ht : 0 ≤ t) (htT : t ≤ T)
    (hγ : 0 ≤ γ) (hγC : γ ≤ C)
    (hf : ∀ u ∈ Icc (-r) 0,
      HasDerivAt f (f₁ (t * Real.exp (u * γ))) (t * Real.exp (u * γ)) ∧
      HasDerivAt f₁ (f₂ (t * Real.exp (u * γ))) (t * Real.exp (u * γ)) ∧
      |f₁ (t * Real.exp (u * γ))| ≤ M ∧ |f₂ (t * Real.exp (u * γ))| ≤ M)
    {u : ℝ} (hu : u ∈ Icc (-r) 0) :
    |f (t * Real.exp (u * γ)) - f t - u * (t * γ * f₁ t)| ≤
      (M * (T * C) ^ 2 + M * (T * C ^ 2)) * u ^ 2 := by
  have hT : 0 ≤ T := ht.trans htT
  have hC : 0 ≤ C := hγ.trans hγC
  let τ : ℝ → ℝ := fun v => t * Real.exp (v * γ)
  let D : ℝ → ℝ := fun v => t * γ * Real.exp (v * γ)
  let D₂ : ℝ → ℝ := fun v => t * γ ^ 2 * Real.exp (v * γ)
  let g : ℝ → ℝ := fun v => f (τ v)
  let g₁ : ℝ → ℝ := fun v => f₁ (τ v) * D v
  let g₂ : ℝ → ℝ := fun v => f₂ (τ v) * D v ^ 2 + f₁ (τ v) * D₂ v
  have hg (v : ℝ) (hv : v ∈ Icc (-r) 0) : HasDerivWithinAt g (g₁ v) (Icc (-r) 0) v :=
    ((hf v hv).1.comp v (exp_clock_hasDerivAt t γ v)).hasDerivWithinAt
  have hg₁ (v : ℝ) (hv : v ∈ Icc (-r) 0) : HasDerivWithinAt g₁ (g₂ v) (Icc (-r) 0) v := by
    have hh := (((hf v hv).2.1.comp v (exp_clock_hasDerivAt t γ v)).mul
      (exp_clock_second_hasDerivAt t γ v))
    convert hh.hasDerivWithinAt (s := Icc (-r) 0) using 1 <;>
      dsimp only [g₁, g₂, D, D₂, τ, Pi.mul_def, Function.comp_def] <;> ring
  have hD (v : ℝ) (hv : v ∈ Icc (-r) 0) : 0 ≤ D v ∧ D v ≤ T * C := by
    have he : Real.exp (v * γ) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hv.2 hγ)
    refine ⟨by dsimp [D]; positivity, ?_⟩
    exact (mul_le_of_le_one_right (mul_nonneg ht hγ) he).trans
      (mul_le_mul htT hγC hγ hT)
  have hD₂ (v : ℝ) (hv : v ∈ Icc (-r) 0) : 0 ≤ D₂ v ∧ D₂ v ≤ T * C ^ 2 := by
    have he : Real.exp (v * γ) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hv.2 hγ)
    refine ⟨by dsimp [D₂]; positivity, ?_⟩
    exact (mul_le_of_le_one_right (mul_nonneg ht (sq_nonneg γ)) he).trans
      (mul_le_mul htT ((sq_le_sq₀ hγ hC).mpr hγC) (sq_nonneg γ) hT)
  have hb (v : ℝ) (hv : v ∈ Icc (-r) 0) : |g₂ v| ≤ M * (T * C) ^ 2 + M * (T * C ^ 2) := by
    calc
      _ ≤ |f₂ (τ v) * D v ^ 2| + |f₁ (τ v) * D₂ v| := abs_add_le _ _
      _ = |f₂ (τ v)| * D v ^ 2 + |f₁ (τ v)| * D₂ v := by
        simp only [abs_mul, abs_of_nonneg (sq_nonneg (D v)), abs_of_nonneg (hD₂ v hv).1]
      _ ≤ _ := add_le_add
        (mul_le_mul (hf v hv).2.2.2 ((sq_le_sq₀ (hD v hv).1 (mul_nonneg hT hC)).mpr (hD v hv).2)
          (sq_nonneg _) hM)
        (mul_le_mul (hf v hv).2.2.1 (hD₂ v hv).2 (hD₂ v hv).1 hM)
  have hh := backward_taylor_bound hr (by positivity) hg hg₁ hb hu
  simpa only [g, g₁, τ, D, zero_mul, Real.exp_zero, mul_one, mul_comm (f₁ t)] using hh

end Yau.Blueprint.V04Proof.ClockTaylorAux
