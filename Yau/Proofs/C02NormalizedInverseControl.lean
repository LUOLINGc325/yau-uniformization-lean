import Yau.Proofs.C02NormalizedInverseSource
import Yau.Proofs.C02InverseImageControl
import Yau.Proofs.C02FrameBounds

/-! A numerical receiving radius controls the actual normalized inverse
source map and keeps its image uniformly inside the normal-coordinate ball. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalization_argument_norm_le (B : E →L[ℝ] E)
    (hB : ‖B - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4)
    (r : ℝ) (hr : 0 < r) (z : E) :
    ‖(Real.sqrt (2 : ℝ) / r) • B z‖ ≤ 3 * ‖z‖ / r := by
  have hRoot : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hr.le)]
  calc
    _ ≤ (2 / r) * ((3 / 2 : ℝ) * ‖z‖) :=
      mul_le_mul (div_le_div_of_nonneg_right hRoot hr.le)
        (close_identity_vector_bounds B hB z).2 (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem normalizedInverseSource_control
    (e : OpenPartialHomeomorph E E) (he0 : (0 : E) ∈ e.source)
    (hClose : ‖fderiv ℝ (e : E → E) 0 - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4)
    (hReceiving : Metric.closedBall (e 0) (3 / 32 : ℝ) ⊆ e.target)
    (hSmooth : ContDiffOn ℝ ∞ e.symm e.target)
    (hDeriv : ∀ y ∈ e.target, ‖fderiv ℝ e.symm y‖ ≤ 2)
    (r : ℝ) (hr : 0 < r) :
    ContDiffOn ℝ ∞ (normalizedInverseSource e r) (Metric.ball 0 (r / 128)) ∧
      ∀ z ∈ Metric.ball (0 : E) (r / 128),
        e 0 + (Real.sqrt (2 : ℝ) / r) • fderiv ℝ (e : E → E) 0 z ∈ e.target ∧
          ‖normalizedInverseSource e r z‖ < r / 8 := by
  let B := fderiv ℝ (e : E → E) 0
  let S := (Real.sqrt (2 : ℝ) / r) • B
  let T := fun z => e 0 + S z
  have hT : ContDiff ℝ ∞ T := contDiff_const.add S.contDiff
  have hPoint (z : E) (hz : z ∈ Metric.ball (0 : E) (r / 128)) :
      T z ∈ e.target ∧ ‖normalizedInverseSource e r z‖ < r / 8 := by
    have hzN : ‖z‖ < r / 128 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hS : ‖S z‖ < (3 / 128 : ℝ) :=
      (normalization_argument_norm_le B hClose r hr z).trans_lt
        ((div_lt_iff₀ hr).mpr (by nlinarith))
    have hR : T z ∈ Metric.closedBall (e 0) (3 / 32 : ℝ) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      change ‖e 0 + S z - e 0‖ ≤ _
      rw [add_sub_cancel_left]
      linarith
    have hPosition := inverse_position_bound_on_receiving_ball e he0 (3 / 32)
      (by norm_num) hReceiving hSmooth hDeriv (T z) hR
    have hSmall : ‖e.symm (T z)‖ < (1 / 8 : ℝ) := by
      have hEq : T z - e 0 = S z := by dsimp only [T]; abel
      rw [hEq] at hPosition
      linarith
    refine ⟨hReceiving hR, ?_⟩
    change ‖r • e.symm (T z)‖ < _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_lt_mul_of_pos_left hSmall hr).trans_eq (by ring)
  refine ⟨?_, hPoint⟩
  exact (hSmooth.comp hT.contDiffOn (fun z hz => (hPoint z hz).1)).const_smul r

end Yau.Blueprint.C02Proof
