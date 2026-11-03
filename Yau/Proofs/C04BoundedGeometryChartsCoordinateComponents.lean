import Yau.Proofs.C04BoundedGeometryChartsEllipticBounds
import Yau.Proofs.C04BoundedGeometryChartsCoordinateFunction

/-! Components of the same normalized coordinates have the actual complex equation and fixed L2 mass. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem coordinate_component_fderiv (F : ComplexVector n → ComplexVector n)
    (x : ComplexVector n) (hF : DifferentiableAt ℝ F x) (k : Fin n) (v : ComplexVector n) :
    fderiv ℝ (fun y => F y k) x v = fderiv ℝ F x v k := by
  let pr : ComplexVector n →L[ℝ] ℂ := (EuclideanSpace.proj k).restrictScalars ℝ
  have H := (pr.hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  change fderiv ℝ (pr ∘ F) x v = pr (fderiv ℝ F x v)
  rw [H]
  rfl

theorem coordinate_component_complex (F : ComplexVector n → ComplexVector n)
    (hF : ContDiff ℝ ∞ F) (J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hrel : ∀ y ∈ O, ∀ v, fderiv ℝ F y (J y v) = Complex.I • fderiv ℝ F y v)
    {x : ComplexVector n} (hx : x ∈ O) (k : Fin n) :
    ∀ᶠ y in 𝓝 x, ∀ v, fderiv ℝ (fun z => F z k) y (J y v) =
      Complex.I * fderiv ℝ (fun z => F z k) y v := by
  filter_upwards [hO.mem_nhds hx] with y hy
  intro v
  rw [coordinate_component_fderiv F y (hF.differentiable (by simp) y),
    coordinate_component_fderiv F y (hF.differentiable (by simp) y)]
  exact congrArg (fun w : ComplexVector n => w k) (hrel y hy v)

theorem smooth_bounded_sobolev_zero_le_volume
    (u : ComplexVector n → ℂ) (hu : ContDiff ℝ ∞ u) (r : ℝ)
    (hbound : ∀ x ∈ Metric.ball (0 : ComplexVector n) r, ‖u x‖ ≤ 1) :
    Yau.LeafCandidates.sobolevNormSq (Metric.ball (0 : ComplexVector n) r) u 0 ≤
      (lebesgueC n (Metric.ball (0 : ComplexVector n) r)).toReal := by
  have hfin : lebesgueC n (Metric.ball (0 : ComplexVector n) r) < ⊤ := by
    rw [lebesgueC_eq_volume]
    exact (measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : ComplexVector n) r).measure_lt_top
  have huI : IntegrableOn (fun x => ‖u x‖^2) (Metric.ball (0 : ComplexVector n) r) (lebesgueC n) := by
    simpa only [norm_iteratedFDeriv_zero] using smooth_iterated_derivative_sq_integrable_ball hu 0 r
  have hc : IntegrableOn (fun _ : ComplexVector n => (1 : ℝ))
      (Metric.ball (0 : ComplexVector n) r) (lebesgueC n) := integrableOn_const hfin.ne
  have H := setIntegral_mono_on huI hc measurableSet_ball (fun x hx => by
    have hb := hbound x hx
    nlinarith [norm_nonneg (u x)])
  simpa only [Yau.LeafCandidates.sobolevNormSq, Nat.zero_add, Finset.sum_range_one,
    norm_iteratedFDeriv_zero, integral_const, Measure.real, smul_eq_mul, mul_one,
    Measure.restrict_apply_univ] using H

theorem coordinate_component_mass_bound (F : ComplexVector n → ComplexVector n)
    (hF : ContDiff ℝ ∞ F)
    (hbound : ∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ‖F x‖ ≤ 1) (k : Fin n) :
    Yau.LeafCandidates.sobolevNormSq (Metric.ball (0 : ComplexVector n) (3 / 8 : ℝ))
      (fun x => F x k) 0 ≤ (lebesgueC n (Metric.ball (0 : ComplexVector n) (3 / 8 : ℝ))).toReal := by
  apply smooth_bounded_sobolev_zero_le_volume _
    (((EuclideanSpace.proj k).restrictScalars ℝ).contDiff.comp hF) (3 / 8)
  intro x hx
  exact (PiLp.norm_apply_le (F x) k).trans (hbound x (Metric.ball_subset_ball (by norm_num) hx))

end Yau.Proofs.C04ChartsAux
