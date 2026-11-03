import Yau.Proofs.Y03GraphExtension

/-! Construct the inverse of a quantitatively injective projection on its actual image. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ H]

theorem exists_projected_inverse (A : Submodule ℂ H) (p : H →L[ℂ] E) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ a : A, ‖a‖ ≤ C * ‖p a‖) :
    ∃ R : LinearMap.range (p.toLinearMap.comp A.subtype) →L[ℂ] H,
      p.comp R = (LinearMap.range (p.toLinearMap.comp A.subtype)).subtypeL ∧
        LinearMap.range R.toLinearMap = A ∧ ‖R‖ ≤ C := by
  let f := p.toLinearMap.comp A.subtype
  have hf : Function.Injective f := by
    intro a b hab
    have hz : p ((a - b : A) : H) = 0 := by
      change f (a - b) = 0
      rw [map_sub, hab, sub_self]
    have hn := hbound (a - b)
    rw [hz, norm_zero, mul_zero] at hn
    exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm hn (norm_nonneg _)))
  let e := LinearEquiv.ofInjective f hf
  let R : LinearMap.range f →L[ℂ] H := A.subtypeL.comp e.symm.toLinearMap.toContinuousLinearMap
  have hright : p.comp R = (LinearMap.range f).subtypeL := by
    ext y
    change f (e.symm y) = y.1
    exact congrArg Subtype.val (e.apply_symm_apply y)
  have hrecovery (a : A) : R (e a) = (a : H) := by
    change ((e.symm (e a) : A) : H) = _
    rw [e.symm_apply_apply]
  refine ⟨R, hright, ?_, ?_⟩
  · apply le_antisymm
    · rintro z ⟨y, rfl⟩
      exact (e.symm y).property
    · intro z hz
      exact ⟨e ⟨z, hz⟩, hrecovery ⟨z, hz⟩⟩
  · refine R.opNorm_le_bound hC ?_
    intro y
    have hb := hbound (e.symm y)
    have hy : p (R y) = y.1 := congrArg (fun L : LinearMap.range f →L[ℂ] E => L y) hright
    change ‖R y‖ ≤ C * ‖p (R y)‖ at hb
    rw [hy] at hb
    exact hb

end Yau.Blueprint.Alignment.Y03Proof
