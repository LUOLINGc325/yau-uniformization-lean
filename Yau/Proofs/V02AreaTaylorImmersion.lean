import Yau.Proofs.V02AreaTaylorQuadratic
import Yau.Proofs.V03TransitionInverse

/-! Compact families of genuine injective differentials have one uniform
left estimate, including an empty parameter compact and zero-dimensional domain. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof

variable {D E F : Type*} [TopologicalSpace D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_injective_linear_family_bound {K : Set D} (hK : IsCompact K)
    {A : D → E →L[ℝ] F} (hA : ContinuousOn A K)
    (hinj : ∀ p ∈ K, Function.Injective (A p)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ v : E, ‖v‖ ≤ C * ‖A p v‖ := by
  let S := K ×ˢ Metric.sphere (0 : E) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  have hc : ContinuousOn (fun p : D × E => ‖A p.1 p.2‖) S :=
    ((hA.comp continuous_fst.continuousOn (fun p hp => hp.1)).clm_apply
      continuous_snd.continuousOn).norm
  by_cases hne : S.Nonempty
  · obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hne hc
    have hpn : ‖p.2‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hp.2
    have hpv : p.2 ≠ 0 := by intro h; simpa [h] using hpn
    have hm : 0 < ‖A p.1 p.2‖ := norm_pos_iff.mpr (by
      intro h
      exact hpv (hinj p.1 hp.1 (by simpa using h)))
    refine ⟨‖A p.1 p.2‖⁻¹, inv_nonneg.mpr hm.le, fun u hu v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    have hn : ‖NormedSpace.normalize v‖ = 1 := NormedSpace.norm_normalize hv
    have hnorm := hmin (show (u, NormedSpace.normalize v) ∈ S from
      ⟨hu, by simpa only [Metric.mem_sphere, dist_zero_right] using hn⟩)
    have hmul : ‖A p.1 p.2‖ * ‖v‖ ≤ ‖A u v‖ := by
      have hh := mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)
      simp only [NormedSpace.normalize, map_smul, norm_smul, norm_inv, norm_norm] at hh
      convert hh using 1 <;> field_simp [norm_ne_zero_iff.mpr hv]
    calc
      ‖v‖ = ‖A p.1 p.2‖⁻¹ * (‖A p.1 p.2‖ * ‖v‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]
      _ ≤ ‖A p.1 p.2‖⁻¹ * ‖A u v‖ := mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hm.le)
  · refine ⟨0, le_rfl, fun p hp v => ?_⟩
    have hv : v = 0 := by
      by_contra h
      have hn : ‖NormedSpace.normalize v‖ = 1 := NormedSpace.norm_normalize h
      exact hne ⟨(p, NormedSpace.normalize v), hp,
        by simpa only [Metric.mem_sphere, dist_zero_right] using hn⟩
    simp [hv]

end Yau.Blueprint.V02AreaTaylorProof
