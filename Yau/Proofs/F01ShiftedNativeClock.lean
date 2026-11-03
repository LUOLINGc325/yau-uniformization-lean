import Yau.Proofs.F01ShiftedNativePotential
import Yau.Proofs.F01SmoothPotentialWordEquations
import Yau.Proofs.F01NormalizedBackgroundRegularity

/-! Shifted positive-time profiles satisfy the original nonlinear
clock equation and hence the complete native spatial word system.
Every identity follows from the same original potential and metric. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem shifted_native_clock_jet
    (A : BoundedChartFamily g) (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    {T ρ τ : ℝ} (hρ : ρ ≠ 0) (hLower : ρ ^ 2 ≤ τ) (hUpper : τ + ρ ^ 2 ≤ T)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio g h x s) (Icc 0 T) s) (a : M.Carrier)
    (x : Space n) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    HasDerivWithinAt (fun s => shiftedNativePotential A U a ρ τ (x, s))
      (flowLogDetRatio g h (A.chart a (affineParabolicPoint ρ 0 τ (x, t)).1)
        (affineParabolicPoint ρ 0 τ (x, t)).2) (Icc (-1) 1) t := by
  have hClock := shifted_clock_maps hLower hUpper
  have hArg : HasDerivWithinAt (fun s : ℝ => τ + ρ ^ 2 * s) (ρ ^ 2) (Icc (-1) 1) t := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id t).const_mul (ρ ^ 2)).const_add τ).hasDerivWithinAt
  have hc := ((hpde (A.chart a (ρ • x + 0)) (τ + ρ ^ 2 * t) (hClock ht)).comp t hArg hClock).const_mul
    ((ρ ^ 2)⁻¹)
  convert hc using 1
  · rfl
  · dsimp only [affineParabolicPoint]
    field_simp [pow_ne_zero 2 hρ]

theorem shifted_native_log_identity
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ τ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hLower : ρ ^ 2 ≤ τ) (hUpper : τ + ρ ^ 2 ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (a : M.Carrier) {p : Point n} (hp : p ∈ cylinder (ball 0 1) (-1) 1) :
    flowLogDetRatio g h (A.chart a (affineParabolicPoint ρ 0 τ p).1)
      (affineParabolicPoint ρ 0 τ p).2 =
      Real.log (chartPotentialMatrix (shiftedComplexBackground A a ρ τ)
        (shiftedNativePotential A U a ρ τ) p).det.re + normalizedPotentialLogSource A a ρ p.1 := by
  rw [shifted_native_flow_matrix hg A h U hρ hρr hLower hUpper hU hpot a hp]
  have hz := shifted_space_maps A hρ hρr hp.1
  have hs := A.closedBall_source a (ball_subset_closedBall hz)
  have hh := flowLogDetRatio_pullback_difference g h (A.chart a)
    (A.differentiable a) (A.inverse_differentiable a) hs (affineParabolicPoint ρ 0 τ p).2
  simpa only [normalizedPotentialLogSource, BoundedChartFamily.backgroundLogDet,
    affineParabolicPoint, add_zero, sub_eq_add_neg] using hh

end Yau.NodeProofs.F01Aux
