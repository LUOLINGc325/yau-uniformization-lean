import Yau.LeafProofs.L05AutonomousSpatialGradientMatrix
import Yau.LeafProofs.L05AutonomousSpatialGradientLimit

open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius Interval
noncomputable section
set_option maxHeartbeats 2400000
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Actual smooth approximations with a Frobenius Hessian budget identify a jointly continuous
native gradient of the original uniform limit, with spatial C1,1 and exact segment FTC. -/
theorem autonomous_spatial_gradient_limit (n : ℕ) (r R a b : ℝ)
    (hr : 0 < r) (hrR : r < R) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ M H : ℝ, 0 ≤ M → 0 ≤ H →
      ∀ u : Point n → ℝ, ContinuousOn u (spatialGradientCylinder (Space n) R a b) →
      ∀ f : ℕ → Point n → ℝ,
        (∀ j, ContinuousOn (f j) (spatialGradientCylinder (Space n) R a b)) →
        (∀ j, ContinuousOn (spatialGradientOf (f j)) (spatialGradientCylinder (Space n) R a b)) →
        (∀ j, ∀ t ∈ Icc a b, ContDiff ℝ ∞ (fun x => f j (x,t))) →
        (∀ j, ∀ p ∈ spatialGradientCylinder (Space n) R a b, |f j p| ≤ M) →
        (∀ j, ∀ p ∈ spatialGradientCylinder (Space n) R a b,
          ‖secondFDerivMatrix (fun x => f j (x,p.2)) p.1‖ ≤ H) →
        TendstoUniformlyOn f u atTop (spatialGradientCylinder (Space n) R a b) →
        ∃ G : Point n → (Space n →L[ℝ] ℝ),
          ContinuousOn G (spatialGradientCylinder (Space n) r a b) ∧
          TendstoUniformlyOn (fun j => spatialGradientOf (f j)) G atTop (spatialGradientCylinder (Space n) r a b) ∧
          (∀ p ∈ spatialGradientCylinder (Space n) r a b, ‖G p‖ ≤ C*(M+H)) ∧
          (∀ t ∈ Icc a b, ∀ x ∈ closedBall (0 : Space n) r,
            HasFDerivAt (fun y => u (y,t)) (G (x,t)) x) ∧
          (∀ t ∈ Icc a b, ∀ x ∈ closedBall (0 : Space n) r, ∀ y ∈ closedBall (0 : Space n) r,
            ‖G (x,t)-G (y,t)‖ ≤ C*H*‖x-y‖) ∧
          (∀ t ∈ Icc a b, ∀ x ∈ closedBall (0 : Space n) r, ∀ y ∈ closedBall (0 : Space n) r,
            |u (y,t)-u (x,t)-G (x,t) (y-x)| ≤ C*H*‖y-x‖^2) ∧
          (∀ t ∈ Icc a b, ∀ x ∈ closedBall (0 : Space n) r, ∀ y ∈ closedBall (0 : Space n) r,
            u (y,t)-u (x,t)=∫ s in (0 : ℝ)..1, G (x+s • (y-x),t) (y-x)) := by
  let s := (r+R)/2
  let step := min 1 ((R-s)/2)
  let D := spatialGradientDimensionBudget n
  let C := 1+2/step+2*D
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  have hstep : 0 < step := lt_min (by norm_num) (by dsimp [s]; linarith)
  have hstep1 : step ≤ 1 := min_le_left _ _
  have hbuffer : s+step ≤ R := by have := min_le_right (1 : ℝ) ((R-s)/2); dsimp [step]; linarith
  have hD : 0 < D := spatialGradientDimensionBudget_pos n
  have hC : 0 < C := by dsimp [C]; positivity
  have hCD : D ≤ C := by dsimp [C]; have := div_pos (by norm_num : (0 : ℝ) < 2) hstep; linarith
  refine ⟨C,hC,?_⟩
  intro M H hM hH u huc f hfc hgc hSmooth hVal hHess hUniform
  let B := D*H
  have hB : 0 ≤ B := mul_nonneg hD.le hH
  have hOp : ∀ j, ∀ p ∈ spatialGradientCylinder (Space n) R a b,
      ‖fderiv ℝ (fderiv ℝ (fun x => f j (x,p.2))) p.1‖ ≤ B := by
    intro j p hp
    exact (spatialGradient_second_derivative_bound _ _).trans
      (mul_le_mul_of_nonneg_left (hHess j p hp) hD.le)
  obtain ⟨G,hCont,hG⟩ := spatialGradient_exists_uniform_limit hsR hB f u hSmooth hOp hgc hUniform
  have hsmall : spatialGradientCylinder (Space n) r a b ⊆ spatialGradientCylinder (Space n) s a b :=
    fun p hp => ⟨closedBall_subset_closedBall hrs.le hp.1,hp.2⟩
  have hlarge : spatialGradientCylinder (Space n) s a b ⊆ spatialGradientCylinder (Space n) R a b :=
    fun p hp => ⟨closedBall_subset_closedBall hsR.le hp.1,hp.2⟩
  have hContR := hCont.mono hsmall
  have hGR := hG.mono hsmall
  have hNative := spatialGradient_limit_hasFDerivAt hrs f u G hSmooth (hUniform.mono hlarge) hG
  have hSup := spatialGradient_limit_sup hstep hbuffer hB hM f G hSmooth hOp hVal hG
  have hNum : 2*M/step+2*B*step ≤ C*(M+H) := by
    have hst : B*step ≤ B := mul_le_of_le_one_right hB hstep1
    have hi : 0 ≤ 2/step := by positivity
    have hCM : 2/step ≤ C := by dsimp [C]; linarith
    have hCH : 2*D ≤ C := by dsimp [C]; linarith
    calc
      _ ≤ (2/step)*M + (2*D)*H := by
        change 2*M/step+2*(D*H)*step ≤ (2/step)*M+(2*D)*H
        change (D*H)*step ≤ D*H at hst
        rw [show 2*M/step = (2/step)*M by ring]
        nlinarith only [hst]
      _ ≤ C*M + C*H := add_le_add
        (mul_le_mul_of_nonneg_right hCM hM) (mul_le_mul_of_nonneg_right hCH hH)
      _ = C*(M+H) := by ring
  refine ⟨G,hContR,hGR,fun p hp => (hSup p (hsmall hp)).trans hNum,hNative,?_,?_,
    spatialGradient_actual_segment_FTC u G hContR hNative⟩
  · intro t ht x hx y hy
    exact (spatialGradient_limit_lipschitz hrR.le f G hSmooth hOp hGR t ht x hx y hy).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCD hH) (norm_nonneg _))
  · intro t ht x hx y hy
    exact (spatialGradient_limit_remainder hrR.le hB f u G hSmooth hOp hUniform hGR t ht x hx y hy).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCD hH) (sq_nonneg _))

end Yau.LeafProofs.L05AutonomousAux
