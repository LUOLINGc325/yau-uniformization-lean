import spec.CHAIN.LeafObligations

/-! Compact localization of the original affine contacts in Jensen's lemma. -/

open Set MeasureTheory
open scoped InnerProductSpace

namespace Yau.LeafProofs.L04Aux

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

theorem boundaryGap_compact_core
    (φ : E → ℝ) (xh : E) (r : ℝ) (O : Set E)
    (hr : 0 < r) (hO : IsOpen O) (hxh : xh ∈ O)
    (hD : IsCompact (closure O))
    (hball : closure O ⊆ Metric.ball xh r)
    (hcont : ContinuousOn φ (closure O))
    (hgap : ∀ y ∈ closure O \ O, φ xh < φ y) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ K : Set E,
      IsCompact K ∧ K ⊆ O ∧
      (∀ x ∈ K, Metric.closedBall x ρ ⊆ O) ∧
      (∀ (x p : E), x ∈ closure O → ‖p‖ ≤ δ₀ →
        (∀ z ∈ closure O,
          φ x - ⟪p, x⟫_ℝ ≤ φ z - ⟪p, z⟫_ℝ) → x ∈ K) := by
  have hB : IsCompact (closure O \ O) := hD.diff hO
  obtain ⟨η, hη, hηgap⟩ : ∃ η : ℝ, 0 < η ∧
      ∀ y ∈ closure O \ O, φ xh + η ≤ φ y := by
    by_cases hne : (closure O \ O).Nonempty
    · obtain ⟨b, hb, hbmin⟩ := hB.exists_isMinOn hne (hcont.mono sdiff_subset)
      refine ⟨φ b - φ xh, sub_pos.mpr (hgap b hb), ?_⟩
      intro y hy
      have := hbmin hy
      dsimp at this
      linarith
    · refine ⟨1, by norm_num, ?_⟩
      intro y hy
      exact (hne ⟨y, hy⟩).elim
  let δ₀ := η / (2 * r)
  have hδ₀ : 0 < δ₀ := div_pos hη (by positivity)
  let K : Set E := closure O ∩ φ ⁻¹' Iic (φ xh + η / 2)
  have hK : IsCompact K :=
    hcont.lowerSemicontinuousOn.isCompact_inter_preimage_Iic hD _
  have hKO : K ⊆ O := by
    intro x hx
    by_contra hxO
    have hbound := hηgap x ⟨hx.1, hxO⟩
    have hxval : φ x ≤ φ xh + η / 2 := hx.2
    linarith
  obtain ⟨ρ, hρ, hthick⟩ := hK.exists_cthickening_subset_open hO hKO
  refine ⟨δ₀, hδ₀, ρ, hρ, K, hK, hKO, ?_, ?_⟩
  · intro x hx
    exact (Metric.closedBall_subset_cthickening hx ρ).trans hthick
  · intro x p hx hp hmin
    refine ⟨hx, ?_⟩
    have hminxh := hmin xh (subset_closure hxh)
    have hnorm : ‖x - xh‖ ≤ r := by
      exact le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hball hx)
    have hinner : ⟪p, x - xh⟫_ℝ ≤ δ₀ * r :=
      (real_inner_le_norm _ _).trans (mul_le_mul hp hnorm (norm_nonneg _) hδ₀.le)
    rw [inner_sub_right] at hinner
    have hprod : δ₀ * r = η / 2 := by
      dsimp [δ₀]
      field_simp
    change φ x ≤ φ xh + η / 2
    rw [hprod] at hinner
    linarith

end Yau.LeafProofs.L04Aux

namespace Yau.LeafProofs

theorem infConvolutionAttainment : Yau.LeafCandidates.InfConvolutionAttainment := by
  intro m K v hK hne hv q κ _hκ
  have hpen : Continuous (fun w : Yau.LeafCandidates.RV m =>
      ‖q - w‖ ^ 2 / (2 * κ)) := by fun_prop
  obtain ⟨z, hz, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hK
    (hv.add hpen.continuousOn.lowerSemicontinuousOn)
  exact ⟨z, hz, fun w hw => hmin hw⟩

end Yau.LeafProofs
