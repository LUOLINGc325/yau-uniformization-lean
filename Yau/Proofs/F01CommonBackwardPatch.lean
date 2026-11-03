import Yau.Proofs.F01BufferedParabolicPatches

/-! Two parabolically close points lie in one actual backward patch.
The common upper face is the later of their two times, so points at a
closed initial or final time face are included. -/
noncomputable section
open Set Metric
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem close_pair_common_backward_patch {κ : ℝ} (hκ : 0 < κ)
    (p q : Point n) (hSpace : ‖p.1 - q.1‖ < κ) (hTime : |p.2 - q.2| < κ ^ 2) :
    ∃ p' q' : Point n, p' ∈ backward 1 ∧ q' ∈ backward 1 ∧
      affineParabolicPoint κ p.1 (max p.2 q.2) p' = p ∧
      affineParabolicPoint κ p.1 (max p.2 q.2) q' = q := by
  let τ := max p.2 q.2
  let inv := affineParabolicPoint κ⁻¹ (-(κ⁻¹ • p.1)) (-τ / κ ^ 2)
  have hsq : 0 < κ ^ 2 := sq_pos_of_pos hκ
  have hTimeInv (z : Point n) : (inv z).2 = (z.2 - τ) / κ ^ 2 := by
    dsimp only [inv, affineParabolicPoint]
    field_simp
    ring
  have hClock {t : ℝ} (ht : t ≤ τ) (hGap : τ - t ≤ |p.2 - q.2|) :
      (t - τ) / κ ^ 2 ∈ Ioc (-1) 0 := by
    constructor
    · apply (lt_div_iff₀ hsq).mpr
      nlinarith
    · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hsq.le
  have hBounds := pair_common_clock_bounds p q
  have hpTime : (inv p).2 ∈ Ioc (-1) 0 := by
    rw [hTimeInv]
    exact hClock (le_max_left _ _) hBounds.2.1
  have hqTime : (inv q).2 ∈ Ioc (-1) 0 := by
    rw [hTimeInv]
    exact hClock (le_max_right _ _) hBounds.2.2.2
  have hpSpace : (inv p).1 = 0 := by
    dsimp only [inv, affineParabolicPoint]
    abel
  have hqSpace : (inv q).1 = κ⁻¹ • (q.1 - p.1) := by
    dsimp only [inv, affineParabolicPoint]
    rw [smul_sub]
    abel
  have hqNorm : ‖(inv q).1‖ < 1 := by
    rw [hqSpace, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hκ]
    calc
      κ⁻¹ * ‖q.1 - p.1‖ = ‖q.1 - p.1‖ / κ := by ring
      _ < 1 := (div_lt_one hκ).mpr (by simpa only [norm_sub_rev] using hSpace)
  refine ⟨inv p, inv q, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [mem_ball, dist_zero_right, hpSpace, norm_zero]; norm_num,
      by simpa only [one_pow] using hpTime⟩
  · exact ⟨mem_ball.mpr (by simpa only [dist_zero_right] using hqNorm),
      by simpa only [one_pow] using hqTime⟩
  · exact affineParabolicPoint_inverse_right hκ.ne' p.1 τ p
  · exact affineParabolicPoint_inverse_right hκ.ne' p.1 τ q

end Yau.NodeProofs.F01Aux
