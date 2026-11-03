import Yau.Proofs.F03JointSpatialWords
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Genuine spatial differentiation and C-infinity of finite integrals of smooth derivative words. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace α]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

def spatialWordIntegral (μ : Measure α) (F : α → E → ℝ) (w : List E) (x : E) : ℝ :=
  ∫ a,directionalWordDerivative (F a) w x ∂μ

theorem spatialWordIntegral_hasFDerivAt
    (μ : Measure α) [IsFiniteMeasure μ] (F : α → E → ℝ) {O : Set E} (hO : IsOpen O)
    (hF : ∀ a,ContDiffOn ℝ ∞ (F a) O)
    (hMeas : ∀ w x,x ∈ O → AEStronglyMeasurable (fun a => directionalWordDerivative (F a) w x) μ)
    (hMeasD : ∀ w x,x ∈ O → AEStronglyMeasurable (fun a => fderiv ℝ (directionalWordDerivative (F a) w) x) μ)
    (hLocal : ∀ x ∈ O,∃ r : ℝ,0 < r ∧ Metric.ball x r ⊆ O ∧
      ∀ w : List E,∃ C : ℝ,∀ a,∀ z ∈ Metric.ball x r,|directionalWordDerivative (F a) w z| ≤ C)
    (w : List E) {x : E} (hx : x ∈ O) :
    ∃ D : E →L[ℝ] ℝ,HasFDerivAt (spatialWordIntegral μ F w) D x ∧
      ∀ v,D v=spatialWordIntegral μ F (v::w) x := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨r,hr,hBall,hBound⟩ := hLocal x hx
  have hxBall : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  let D : E → α → E →L[ℝ] ℝ := fun z a => fderiv ℝ (directionalWordDerivative (F a) w) z
  have hPoint (v : E) : ∃ C : ℝ,∀ i : α × Metric.ball x r,‖D i.2.val i.1 v‖ ≤ C := by
    obtain ⟨C,hC⟩ := hBound (v::w)
    refine ⟨C,fun i => ?_⟩
    simpa only [D,directionalWordDerivative,Real.norm_eq_abs] using hC i.1 i.2.val i.2.property
  obtain ⟨C,hC⟩ := banach_steinhaus (g := fun i : α × Metric.ball x r => D i.2.val i.1) hPoint
  have hDBound (a : α) (z : E) (hz : z ∈ Metric.ball x r) : ‖D z a‖ ≤ max C 0 :=
    (hC (a,⟨z,hz⟩)).trans (le_max_left _ _)
  have hIntD : Integrable (D x) μ := (integrable_const (max C 0)).mono'
    (hMeasD w x hx) (ae_of_all μ (fun a => hDBound a x hxBall))
  obtain ⟨B,hB⟩ := hBound w
  have hInt : Integrable (fun a => directionalWordDerivative (F a) w x) μ :=
    (integrable_const B).mono' (hMeas w x hx) (ae_of_all μ (fun a => by
      simpa only [Real.norm_eq_abs] using hB a x hxBall))
  have hDerivative : HasFDerivAt (fun z => ∫ a,directionalWordDerivative (F a) w z ∂μ)
      (∫ a,D x a ∂μ) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := D) (bound := fun _ => max C 0)
      (Metric.ball_mem_nhds x hr)
    · filter_upwards [Metric.ball_mem_nhds x hr] with z hz
      exact hMeas w z (hBall hz)
    · exact hInt
    · exact hMeasD w x hx
    · exact ae_of_all μ (fun a z hz => hDBound a z hz)
    · exact integrable_const _
    · exact ae_of_all μ (fun a z hz =>
        ((directionalWordDerivative_contDiffOn hO (hF a) w).contDiffAt
          (hO.mem_nhds (hBall hz))).differentiableAt (by simp) |>.hasFDerivAt)
  refine ⟨∫ a,D x a ∂μ,hDerivative,fun v => ?_⟩
  rw [ContinuousLinearMap.integral_apply hIntD]
  rfl

theorem spatialWordIntegral_contDiffOn
    (μ : Measure α) [IsFiniteMeasure μ] (F : α → E → ℝ) {O : Set E} (hO : IsOpen O)
    (hF : ∀ a,ContDiffOn ℝ ∞ (F a) O)
    (hMeas : ∀ w x,x ∈ O → AEStronglyMeasurable (fun a => directionalWordDerivative (F a) w x) μ)
    (hMeasD : ∀ w x,x ∈ O → AEStronglyMeasurable (fun a => fderiv ℝ (directionalWordDerivative (F a) w) x) μ)
    (hLocal : ∀ x ∈ O,∃ r : ℝ,0 < r ∧ Metric.ball x r ⊆ O ∧
      ∀ w : List E,∃ C : ℝ,∀ a,∀ z ∈ Metric.ball x r,|directionalWordDerivative (F a) w z| ≤ C)
    (w : List E) : ContDiffOn ℝ ∞ (spatialWordIntegral μ F w) O := by
  have hD (w : List E) (x : E) (hx : x ∈ O) :=
    spatialWordIntegral_hasFDerivAt μ F hO hF hMeas hMeasD hLocal w hx
  rw [contDiffOn_infty]
  intro m
  induction m generalizing w with
  | zero =>
    apply contDiffOn_zero.mpr
    intro x hx
    obtain ⟨D,hD,_hEval⟩ := hD w x hx
    exact hD.continuousAt.continuousWithinAt
  | succ m ih =>
    have hdiff : DifferentiableOn ℝ (spatialWordIntegral μ F w) O := by
      intro x hx
      obtain ⟨D,hD,_hEval⟩ := hD w x hx
      exact hD.differentiableAt.differentiableWithinAt
    have hApp (v : E) : ContDiffOn ℝ (m : ℕ∞ω)
        (fun x => fderivWithin ℝ (spatialWordIntegral μ F w) O x v) O := by
      apply (ih (v::w)).congr
      intro x hx
      obtain ⟨D,hD,hEval⟩ := hD w x hx
      rw [hD.hasFDerivWithinAt.fderivWithin (hO.uniqueDiffWithinAt hx)]
      exact hEval v
    simpa only [Nat.cast_add,Nat.cast_one] using
      contDiffOn_succ_of_fderiv_apply hdiff (by simp) hApp

end Yau.Proofs.F03Aux
