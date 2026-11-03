import Yau.Proofs.V02AreaTaylorJet

/-! The actual parameter slice jet at a point needs only the corresponding
finite-order germ. In particular pointwise smoothness suffices. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof

variable {A F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_slice_finite (k : ℕ) {O : Set (ℂ × A)} (hO : IsOpen O) {f : ℂ × A → F}
    (hf : ContDiffOn ℝ (k : ℕ∞ω) f O) {z : ℂ} {a : A} (hza : (z, a) ∈ O) :
    iteratedFDeriv ℝ k (fun w => f (w, a)) z =
      (iteratedFDeriv ℝ k f (z, a)).compContinuousLinearMap
        (fun _ : Fin k => ContinuousLinearMap.inl ℝ ℂ A) := by
  let L := ContinuousLinearMap.inl ℝ ℂ A
  let S := (fun p : ℂ × A => p + (0, a)) ⁻¹' O
  have hS : IsOpen S := hO.preimage (continuous_id.add continuous_const)
  have hL : IsOpen (L ⁻¹' S) := hS.preimage L.continuous
  have hx : L z ∈ S := by simpa [S, L] using hza
  have hshift : ContDiffOn ℝ (k : ℕ∞ω) (fun p : ℂ × A => f (p + (0, a))) S :=
    hf.comp (contDiff_id.add contDiff_const).contDiffOn (fun p hp => hp)
  have h := L.iteratedFDerivWithin_comp_right hshift hS.uniqueDiffOn hL.uniqueDiffOn hx
    (i := k) (by simp)
  rw [iteratedFDerivWithin_of_isOpen k hL hx,
    iteratedFDerivWithin_of_isOpen k hS hx,
    iteratedFDeriv_comp_add_right] at h
  simpa only [Function.comp_def, L, ContinuousLinearMap.inl_apply, Prod.mk_add_mk,
    zero_add, add_zero] using h


theorem iteratedFDeriv_slice_at {f : ℂ × A → F} {z : ℂ} {a : A}
    (hf : ContDiffAt ℝ ∞ f (z, a)) (k : ℕ) :
    iteratedFDeriv ℝ k (fun w => f (w, a)) z =
      (iteratedFDeriv ℝ k f (z, a)).compContinuousLinearMap
        (fun _ : Fin k => ContinuousLinearMap.inl ℝ ℂ A) := by
  obtain ⟨O, hO, hza, hlocal⟩ := hf.contDiffOn' (m := (k : ℕ∞ω)) (by simp) (by simp)
  have hlocal' : ContDiffOn ℝ (k : ℕ∞ω) f O := by simpa using hlocal
  exact iteratedFDeriv_slice_finite k hO hlocal' hza

theorem norm_iteratedFDeriv_slice_at_le {f : ℂ × A → F} {z : ℂ} {a : A}
    (hf : ContDiffAt ℝ ∞ f (z, a)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w => f (w, a)) z‖ ≤ ‖iteratedFDeriv ℝ k f (z, a)‖ := by
  rw [iteratedFDeriv_slice_at hf k]
  exact ((iteratedFDeriv ℝ k f (z, a)).norm_compContinuousLinearMap_le
    (fun _ : Fin k => ContinuousLinearMap.inl ℝ ℂ A)).trans (by
      apply mul_le_of_le_one_right (norm_nonneg _)
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
        (fun _ _ => ContinuousLinearMap.norm_inl_le_one ℝ ℂ A))

theorem compact_slice_jet_bound_at {f : ℂ × A → F} {K : Set (ℂ × A)}
    (hK : IsCompact K) (hf : ∀ p ∈ K, ContDiffAt ℝ ∞ f p) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1‖ ≤ C := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ k f) K := fun p hp =>
    ((hf p hp).differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k : (k : ℕ∞ω) < ∞)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hcont).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun p hp => ?_⟩
  exact (norm_iteratedFDeriv_slice_at_le (hf p hp) k).trans
    ((hC _ ⟨p, hp, rfl⟩).trans (le_max_left _ _))

end Yau.Blueprint.V02AreaTaylorProof
