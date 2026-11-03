import Yau.Proofs.C02QuantitativeInverse
import Yau.Proofs.C02OperatorSmoothInverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! The fixed-radius inverse is the actual smooth inverse on its open
target, and its differential is the actual inverse differential. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_fixed_ball_smooth_inverse (f : E → E) (R : ℝ) (hR : 0 < R)
    (hf : ContDiff ℝ ∞ f)
    (hClose : ∀ x ∈ Metric.ball (0 : E) R,
      ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = f ∧
      e.source = Metric.ball (0 : E) R ∧
      Metric.closedBall (f 0) (3 * R / 8) ⊆ e.target ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ y ∈ e.target,
        fderiv ℝ e.symm y = (fderiv ℝ f (e.symm y)).inverse ∧ ‖fderiv ℝ e.symm y‖ ≤ 2 := by
  obtain ⟨e, he, hSource, hTarget⟩ := exists_fixed_ball_inverse f R hR hf hClose
  have hBack (y : E) (hy : y ∈ e.target) : e.symm y ∈ Metric.ball (0 : E) R := by
    rw [← hSource]
    exact e.map_target hy
  have hPoint (y : E) (hy : y ∈ e.target) :
      ContDiffAt ℝ ∞ e.symm y ∧
        fderiv ℝ e.symm y = (fderiv ℝ f (e.symm y)).inverse := by
    have hInv := isInvertible_of_close_identity (fderiv ℝ f (e.symm y))
      (hClose (e.symm y) (hBack y hy))
    obtain ⟨L, hL⟩ := hInv
    have hfd : HasFDerivAt (e : E → E) (L : E →L[ℝ] E) (e.symm y) := by
      rw [he, hL]
      exact (hf.differentiable (by simp) (e.symm y)).hasFDerivAt
    refine ⟨e.contDiffAt_symm hy hfd (by rw [he]; exact hf.contDiffAt), ?_⟩
    rw [← hL, ContinuousLinearMap.inverse_equiv]
    exact (e.hasFDerivAt_symm hy hfd).fderiv
  refine ⟨e, he, hSource, hTarget, fun y hy => (hPoint y hy).1.contDiffWithinAt, ?_⟩
  intro y hy
  refine ⟨(hPoint y hy).2, ?_⟩
  rw [(hPoint y hy).2]
  exact norm_actual_inverse_of_close_identity (fderiv ℝ f (e.symm y))
    (hClose (e.symm y) (hBack y hy))

end Yau.Blueprint.C02Proof
