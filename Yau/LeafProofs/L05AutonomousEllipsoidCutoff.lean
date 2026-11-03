import Yau.LeafProofs.L05AutonomousCommutatorBound
import Yau.LeafProofs.L05AutonomousEllipsoidViscosity

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The original local function satisfies the true cutoff pairing budget, with no exterior data assumption. -/
theorem auto_original_ellipsoid_cutoff_bound {n : ℕ} {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hcφ : HasCompactSupport φ) {R b : ℝ} (hb : 0≤ b) (hbuffer : R+b< 1)
    (hsupp : tsupport φ⊆Metric.closedBall (0 : Space n) R) :
    ∃ C : ℝ, 0< C ∧ ∀ (B : Space n ≃L[ℝ] Space n) {r L M : ℝ},
      0< r → 0≤ L → 0≤ M → ‖B.toContinuousLinearMap‖≤ b →
      ‖B.toContinuousLinearMap‖^2≤ r^2*L → ∀ u : Point n → ℝ,
      ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p|≤ M) →
      ∀ t∈Icc (-1 : ℝ) 0,
      Integrable (fun x => φ x*autoEllipsoidSecond B r u (x,t)) ∧
        |∫ x, φ x*autoEllipsoidSecond B r u (x,t)|≤ C*M*L := by
  obtain ⟨C,hC,hBudget⟩ := auto_ellipsoid_cutoff_integral_bound hφ hcφ hb hsupp
  refine ⟨C,hC,?_⟩
  intro B r L M hr hL hM hB hBsq u hu huM t ht
  obtain ⟨w,hwu,hw,hcw,hwnorm⟩ := auto_compact_extension ((isCompact_closedBall _ _).prod isCompact_Icc) hu
  have hwM : ‖w‖≤ M := hwnorm M hM huM
  let f : Space n → ℝ := fun x => w (x,t)
  have hf : Continuous f := w.continuous.comp (continuous_id.prodMk continuous_const)
  have hcf : HasCompactSupport f := auto_compact_spatial_slice hcw t
  have hfM (x : Space n) : |f x|≤ M := by
    have hh := w.norm_coe_le_norm (x,t)
    rw [Real.norm_eq_abs] at hh
    exact hh.trans hwM
  have hWInt : Integrable (fun x => φ x*autoEllipsoidSecond B r w (x,t)) := by
    have hi := (auto_ellipsoid_average_commutator B hφ.continuous hf hcφ hcf).1.div_const (r^2)
    simpa only [autoEllipsoidSecond,autoEllipsoidMean,autoSpatialAverage,f,mul_div_assoc] using hi
  have hWBound : |∫ x, φ x*autoEllipsoidSecond B r w (x,t)|≤ C*M*L :=
    hBudget B hr hL hM hB hBsq f hf hcf hfM
  have hEq : (fun x => φ x*autoEllipsoidSecond B r w (x,t))=
      (fun x => φ x*autoEllipsoidSecond B r u (x,t)) := by
    funext x
    by_cases hzero : φ x=0
    · simp only [hzero,zero_mul]
    have hxR : x∈Metric.closedBall (0 : Space n) R := hsupp (subset_tsupport φ hzero)
    have hxNorm : ‖x‖≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hxR
    have hxU : (x,t)∈unitClosed n := by
      refine ⟨?_,ht⟩
      simpa only [Metric.mem_closedBall,dist_zero_right] using hxNorm.trans (by linarith only [hb,hbuffer] : R≤ 1)
    have hAE : (fun y => w (x+y,t)) =ᵐ[autoLinearBallProbability B] (fun y => u (x+y,t)) := by
      filter_upwards [autoLinearBallProbability_ball_ae B hB] with y hy
      apply hwu
      refine ⟨?_,ht⟩
      have hyNorm : ‖y‖≤ b := by simpa only [Metric.mem_closedBall,dist_zero_right] using hy
      have hnorm := (norm_add_le x y).trans_lt (by linarith only [hxNorm,hyNorm,hbuffer] : ‖x‖+‖y‖< 1)
      simpa only [Metric.mem_closedBall,dist_zero_right] using hnorm.le
    change φ x*(((∫ y, w (x+y,t) ∂autoLinearBallProbability B)-w (x,t))/r^2)=
      φ x*(((∫ y, u (x+y,t) ∂autoLinearBallProbability B)-u (x,t))/r^2)
    rw [integral_congr_ae hAE,hwu hxU]
  rw [hEq] at hWInt hWBound
  exact ⟨hWInt,hWBound⟩

end Yau.LeafProofs.L05AutonomousAux
