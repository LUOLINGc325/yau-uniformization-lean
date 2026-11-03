import Mathlib.Analysis.Calculus.MeanValue

/-! Vanishing of the radial derivative gives actual constancy. The
positive-time ray is treated first, then continuity supplies the origin. -/

noncomputable section
open Set
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem eq_origin_of_radial_fderiv_zero {C : E → F} (hC : Differentiable ℝ C)
    (hRad : ∀ y, fderiv ℝ C y y = 0) (x : E) : C x = C 0 := by
  let f := fun t : ℝ => C (t • x)
  have hf : Continuous f := hC.continuous.comp (continuous_id.smul continuous_const)
  have hD (t : ℝ) : HasDerivAt f (fderiv ℝ C (t • x) x) t := by
    simpa only [f, Function.comp_def, id_eq, one_smul] using (hC (t • x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const x)
  have hzero (t : ℝ) (ht : 0 < t) : fderiv ℝ C (t • x) x = 0 := by
    have h := hRad (t • x)
    rw [map_smul] at h
    exact (smul_eq_zero.mp h).resolve_left ht.ne'
  have hconst (t : ℝ) (ht : 0 < t) : f t = f 1 := by
    apply isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
    · intro s hs; exact (hD s).differentiableAt.differentiableWithinAt
    · intro s hs; exact (hD s).deriv.trans (hzero s hs)
    · exact ht
    · norm_num
  have hclosed : IsClosed {t : ℝ | f t = f 1} := isClosed_eq hf continuous_const
  have hsub : Ioi (0 : ℝ) ⊆ {t : ℝ | f t = f 1} := fun t ht => hconst t ht
  have hmem : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by rw [closure_Ioi (0 : ℝ)]; exact le_refl (0 : ℝ)
  have hz : f 0 = f 1 := (closure_minimal hsub hclosed) hmem
  simpa only [f, zero_smul, one_smul] using hz.symm

end Yau.Blueprint.C02Proof
