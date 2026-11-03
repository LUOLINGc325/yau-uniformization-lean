import spec.CHAIN.CONTRACTS

/-! Uniform positive quadratic bounds on an actual compact family. The
zero-dimensional case is handled directly, without a positive-dimension inlet. -/
open Set Metric
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {A E : Type*} [TopologicalSpace A] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem compact_positive_bilinear_bounds {K : Set A} (hK : IsCompact K)
    {B : A → E →L[ℝ] E →L[ℝ] ℝ} (hB : ContinuousOn B K)
    (hpos : ∀ a ∈ K, ∀ v : E, v ≠ 0 → 0 < B a v v) :
    ∃ ℓ C : ℝ, 0 < ℓ ∧ 0 < C ∧ ∀ a ∈ K, ∀ v : E,
      ℓ * ‖v‖ ^ 2 ≤ B a v v ∧ B a v v ≤ C * ‖v‖ ^ 2 := by
  classical
  by_cases hne : K.Nonempty
  · by_cases htriv : Subsingleton E
    · letI := htriv
      refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
      intro a ha v
      have hv : v = 0 := Subsingleton.elim _ _
      simp [hv]
    · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp htriv
      obtain ⟨v₀, hv₀⟩ := exists_ne (0 : E)
      have hnv₀ : ‖v₀‖ ≠ 0 := norm_ne_zero_iff.mpr hv₀
      have hunit₀ : ‖‖v₀‖⁻¹ • v₀‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ hnv₀]
      have hsne : (sphere (0 : E) 1).Nonempty :=
        ⟨‖v₀‖⁻¹ • v₀, by simpa only [mem_sphere, dist_zero_right] using hunit₀⟩
      have hq : ContinuousOn (fun p : A × E => B p.1 p.2 p.2) (K ×ˢ sphere 0 1) :=
        (((hB.comp continuous_fst.continuousOn (fun _ hp => hp.1)).clm_apply
          continuous_snd.continuousOn).clm_apply continuous_snd.continuousOn)
      have hcomp := hK.prod (isCompact_sphere (0 : E) 1)
      obtain ⟨p₀, hp₀, hmin⟩ := hcomp.exists_isMinOn (hne.prod hsne) hq
      have hn₀ : ‖p₀.2‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hp₀.2
      have hvp₀ : p₀.2 ≠ 0 := by intro h; rw [h, norm_zero] at hn₀; norm_num at hn₀
      have hLower : 0 < B p₀.1 p₀.2 p₀.2 := hpos p₀.1 hp₀.1 p₀.2 hvp₀
      obtain ⟨D, hD⟩ := hcomp.exists_bound_of_continuousOn hq
      refine ⟨B p₀.1 p₀.2 p₀.2, max 1 D + 1, hLower, by positivity, ?_⟩
      intro a ha v
      by_cases hv : v = 0
      · simp [hv]
      · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
        let w := ‖v‖⁻¹ • v
        have hwunit : ‖w‖ = 1 := by
          dsimp [w]
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
            inv_mul_cancel₀ hnv]
        have hw : w ∈ sphere (0 : E) 1 := by
          simpa only [mem_sphere, dist_zero_right] using hwunit
        have hrep : ‖v‖ • w = v := by simp [w, smul_smul, hnv]
        have hscale : B a v v = ‖v‖ ^ 2 * B a w w := by
          calc
            B a v v = B a (‖v‖ • w) (‖v‖ • w) :=
              congrArg₂ (fun x y => B a x y) hrep.symm hrep.symm
            _ = ‖v‖ ^ 2 * B a w w := by
              simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
              ring
        have hlo : B p₀.1 p₀.2 p₀.2 ≤ B a w w :=
          hmin (show (a, w) ∈ K ×ˢ sphere (0 : E) 1 from ⟨ha, hw⟩)
        have hup : B a w w ≤ max 1 D + 1 := by
          have hd := hD (a, w) ⟨ha, hw⟩
          have hb : B a w w ≤ D := (le_abs_self _).trans
            (by simpa only [Real.norm_eq_abs] using hd)
          linarith [le_max_right (1 : ℝ) D]
        rw [hscale]
        constructor
        · nlinarith [mul_le_mul_of_nonneg_left hlo (sq_nonneg ‖v‖)]
        · nlinarith [mul_le_mul_of_nonneg_left hup (sq_nonneg ‖v‖)]
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro a ha
    exact False.elim (hne ⟨a, ha⟩)

end Yau.NodeProofs.F01Aux
