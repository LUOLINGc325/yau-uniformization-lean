import Mathlib

namespace Yau.Analysis

variable {𝕜 V H : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A linear functional controlled by a Hilbert-space-valued linear map is represented
by an ambient Hilbert vector with the same norm bound. The source module needs no
norm, and the controlling map needs neither injectivity nor closed range. -/
theorem exists_norm_le_inner_eq_of_range_bound
    (J : V →ₗ[𝕜] H) (f : V →ₗ[𝕜] 𝕜) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ v, ‖f v‖ ≤ C * ‖J v‖) :
    ∃ u : H, ‖u‖ ≤ C ∧ ∀ v, inner 𝕜 u (J v) = f v := by
  classical
  have hker : J.ker ≤ f.ker := by
    intro v hv
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [LinearMap.mem_ker.mp hv, norm_zero, mul_zero] using hbound v
  let g : J.range →ₗ[𝕜] 𝕜 :=
    (J.ker.liftQ f hker).comp J.quotKerEquivRange.symm.toLinearMap
  have hgJ (v : V) : g (J.rangeRestrict v) = f v := by
    change (J.ker.liftQ f hker) (J.quotKerEquivRange.symm ⟨J v, _⟩) = f v
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hg : ∀ x : J.range, ‖g x‖ ≤ C * ‖x‖ := by
    intro x
    obtain ⟨v, rfl⟩ := J.surjective_rangeRestrict x
    change ‖g (J.rangeRestrict v)‖ ≤ C * ‖J v‖
    rw [hgJ]
    exact hbound v
  obtain ⟨F, hF, hFnorm⟩ := exists_extension_norm_eq J.range (g.mkContinuous C hg)
  refine ⟨(InnerProductSpace.toDual 𝕜 H).symm F, ?_, ?_⟩
  · rw [(InnerProductSpace.toDual 𝕜 H).symm.norm_map, hFnorm]
    exact g.mkContinuous_norm_le hC hg
  · intro v
    rw [InnerProductSpace.toDual_symm_apply]
    exact (hF (J.rangeRestrict v)).trans (hgJ v)

/-- Squared-norm form of `exists_norm_le_inner_eq_of_range_bound`, preserving the
exact constant in the squared estimate. -/
theorem exists_sq_norm_le_inner_eq_of_range_bound
    (J : V →ₗ[𝕜] H) (f : V →ₗ[𝕜] 𝕜) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ v, ‖f v‖ ^ 2 ≤ A * ‖J v‖ ^ 2) :
    ∃ u : H, ‖u‖ ^ 2 ≤ A ∧ ∀ v, inner 𝕜 u (J v) = f v := by
  have hnorm : ∀ v, ‖f v‖ ≤ Real.sqrt A * ‖J v‖ := by
    intro v
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg A) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt hA] using hbound v
  obtain ⟨u, hu, huf⟩ := exists_norm_le_inner_eq_of_range_bound
    J f (Real.sqrt A) (Real.sqrt_nonneg A) hnorm
  refine ⟨u, ?_, huf⟩
  have hsq := (sq_le_sq₀ (norm_nonneg u) (Real.sqrt_nonneg A)).mpr hu
  simpa only [Real.sq_sqrt hA] using hsq

end Yau.Analysis
