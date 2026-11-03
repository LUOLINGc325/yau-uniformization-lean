import Yau.LeafProofs.L17ParabolicHolderScaling

/-! The genuine four Gaussian jets after rescaling, with the small first-jet budget retained. -/

noncomputable section

open Set

set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic

variable {n : ℕ}

theorem parabolicUnscale_four_jet_bounds {ρ T α C J : ℝ}
    (hρ : 0 < ρ) (hT : 0 < T) (hα : 0 ≤ α) {u : Point n → ℝ}
    (hu : SchauderBound α (cylinder Set.univ 0 (T / ρ ^ 2)) u C)
    (hjet : HolderBound α (cylinder Set.univ 0 (T / ρ ^ 2))
      (fun p => (u p, spatialD u p)) J) :
    C2 (cylinder Set.univ 0 T) (parabolicUnscale ρ u) ∧
    (∀ p ∈ cylinder Set.univ 0 T,
      |parabolicUnscale ρ u p| ≤ ρ ^ 2 * J ∧
      ‖spatialD (parabolicUnscale ρ u) p‖ ≤ ρ * J ∧
      ‖spatialDD (parabolicUnscale ρ u) p‖ ≤ C ∧
      |timeD (cylinder Set.univ 0 T) (parabolicUnscale ρ u) p| ≤ C) ∧
    ∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T,
      |parabolicUnscale ρ u p - parabolicUnscale ρ u q| ≤
        (2 * ρ ^ 2 * J) * (parabolicDistance p q / ρ) ^ α ∧
      ‖spatialD (parabolicUnscale ρ u) p - spatialD (parabolicUnscale ρ u) q‖ ≤
        (2 * ρ * J) * (parabolicDistance p q / ρ) ^ α ∧
      ‖spatialDD (parabolicUnscale ρ u) p - spatialDD (parabolicUnscale ρ u) q‖ ≤
        (2 * C) * (parabolicDistance p q / ρ) ^ α ∧
      |timeD (cylinder Set.univ 0 T) (parabolicUnscale ρ u) p -
        timeD (cylinder Set.univ 0 T) (parabolicUnscale ρ u) q| ≤
        (2 * C) * (parabolicDistance p q / ρ) ^ α := by
  refine ⟨c2_parabolicUnscale hρ.ne' hT hu.1, ?_, ?_⟩
  · intro p hp
    have hs := parabolicScalePoint_mem_cylinder hρ.ne' hp
    have hv := hjet.2.1 (parabolicScalePoint ρ p) hs
    change max ‖u (parabolicScalePoint ρ p)‖ ‖spatialD u (parabolicScalePoint ρ p)‖ ≤ J at hv
    have hval : |u (parabolicScalePoint ρ p)| ≤ J := by
      simpa only [Real.norm_eq_abs] using (le_max_left _ _).trans hv
    have hgrad := (le_max_right _ _).trans hv
    refine ⟨?_, ?_, ?_, ?_⟩
    · change |ρ ^ 2 * u (parabolicScalePoint ρ p)| ≤ _
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left hval (sq_nonneg _)
    · rw [spatialD_parabolicUnscale hρ.ne', norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      exact mul_le_mul_of_nonneg_left hgrad hρ.le
    · rw [spatialDD_parabolicUnscale hρ.ne']
      exact hu.2.2.2.1.2.1 _ hs
    · rw [timeD_parabolicUnscale hρ.ne' hT hu.1 hp]
      simpa only [Real.norm_eq_abs] using hu.2.2.2.2.2.1 (parabolicScalePoint ρ p) hs
  · intro p hp q hq
    let d := (parabolicDistance p q / ρ) ^ α
    have hj := holderBound_scaled_difference hρ hα hjet hp hq
    change max ‖u (parabolicScalePoint ρ p) - u (parabolicScalePoint ρ q)‖
      ‖spatialD u (parabolicScalePoint ρ p) - spatialD u (parabolicScalePoint ρ q)‖ ≤ 2 * J * d at hj
    have hval : |u (parabolicScalePoint ρ p) - u (parabolicScalePoint ρ q)| ≤ 2 * J * d := by
      simpa only [Real.norm_eq_abs] using (le_max_left _ _).trans hj
    have hgrad := (le_max_right _ _).trans hj
    refine ⟨?_, ?_, ?_, ?_⟩
    · have heq : parabolicUnscale ρ u p - parabolicUnscale ρ u q =
          ρ ^ 2 * (u (parabolicScalePoint ρ p) - u (parabolicScalePoint ρ q)) := by
        dsimp only [parabolicUnscale, parabolicScalePoint]
        ring
      rw [heq, abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact (mul_le_mul_of_nonneg_left hval (sq_nonneg _)).trans_eq (by dsimp [d]; ring)
    · have heq : spatialD (parabolicUnscale ρ u) p - spatialD (parabolicUnscale ρ u) q =
          ρ • (spatialD u (parabolicScalePoint ρ p) - spatialD u (parabolicScalePoint ρ q)) := by
        rw [spatialD_parabolicUnscale hρ.ne', spatialD_parabolicUnscale hρ.ne']
        apply ContinuousLinearMap.ext
        intro v
        change ρ * spatialD u (parabolicScalePoint ρ p) v -
          ρ * spatialD u (parabolicScalePoint ρ q) v =
          ρ * (spatialD u (parabolicScalePoint ρ p) v - spatialD u (parabolicScalePoint ρ q) v)
        ring
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      exact (mul_le_mul_of_nonneg_left hgrad hρ.le).trans_eq (by dsimp [d]; ring)
    · rw [spatialDD_parabolicUnscale hρ.ne', spatialDD_parabolicUnscale hρ.ne']
      exact holderBound_scaled_difference hρ hα hu.2.2.2.1 hp hq
    · rw [timeD_parabolicUnscale hρ.ne' hT hu.1 hp, timeD_parabolicUnscale hρ.ne' hT hu.1 hq]
      simpa only [Real.norm_eq_abs] using
        holderBound_scaled_difference hρ hα hu.2.2.2.2 hp hq

end Yau.LeafProofs.L17Aux
