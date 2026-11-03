import Yau.Proofs.V02AreaTaylorIntegral

/-! Higher jets in an open parameter direction are restrictions of the
actual joint jets. Compactness then bounds homogeneous quadratic kernels. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof

variable {A F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_slice {O : Set (ℂ × A)} (hO : IsOpen O) {f : ℂ × A → F}
    (hf : ContDiffOn ℝ ∞ f O) {z : ℂ} {a : A} (hza : (z, a) ∈ O) (k : ℕ) :
    iteratedFDeriv ℝ k (fun w => f (w, a)) z =
      (iteratedFDeriv ℝ k f (z, a)).compContinuousLinearMap
        (fun _ : Fin k => ContinuousLinearMap.inl ℝ ℂ A) := by
  let L := ContinuousLinearMap.inl ℝ ℂ A
  let S := (fun p : ℂ × A => p + (0, a)) ⁻¹' O
  have hS : IsOpen S := hO.preimage (continuous_id.add continuous_const)
  have hL : IsOpen (L ⁻¹' S) := hS.preimage L.continuous
  have hx : L z ∈ S := by simpa [S, L] using hza
  have hshift : ContDiffOn ℝ ∞ (fun p : ℂ × A => f (p + (0, a))) S :=
    hf.comp (contDiff_id.add contDiff_const).contDiffOn (fun p hp => hp)
  have h := L.iteratedFDerivWithin_comp_right hshift hS.uniqueDiffOn hL.uniqueDiffOn hx
    (i := k) (by simp)
  rw [iteratedFDerivWithin_of_isOpen k hL hx,
    iteratedFDerivWithin_of_isOpen k hS hx,
    iteratedFDeriv_comp_add_right] at h
  simpa only [Function.comp_def, L, ContinuousLinearMap.inl_apply, Prod.mk_add_mk,
    zero_add, add_zero] using h

theorem norm_iteratedFDeriv_slice_le {O : Set (ℂ × A)} (hO : IsOpen O)
    {f : ℂ × A → F} (hf : ContDiffOn ℝ ∞ f O)
    {z : ℂ} {a : A} (hza : (z, a) ∈ O) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w => f (w, a)) z‖ ≤
      ‖iteratedFDeriv ℝ k f (z, a)‖ := by
  rw [iteratedFDeriv_slice hO hf hza k]
  have hb := (iteratedFDeriv ℝ k f (z, a)).norm_compContinuousLinearMap_le
    (fun _ : Fin k => ContinuousLinearMap.inl ℝ ℂ A)
  exact hb.trans (by
    apply mul_le_of_le_one_right (norm_nonneg _)
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun _ _ => ContinuousLinearMap.norm_inl_le_one ℝ ℂ A))

theorem compact_slice_jet_bound {O : Set (ℂ × A)} (hO : IsOpen O)
    {f : ℂ × A → F} (hf : ContDiffOn ℝ ∞ f O)
    {K : Set (ℂ × A)} (hK : IsCompact K) (hKO : K ⊆ O) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv hf hO (by simp : (k : ℕ∞ω) ≤ ∞)).mono hKO)).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun p hp => ?_⟩
  exact (norm_iteratedFDeriv_slice_le hO hf (hKO hp) k).trans
    ((hC _ ⟨p, hp, rfl⟩).trans (le_max_left _ _))

end Yau.Blueprint.V02AreaTaylorProof
