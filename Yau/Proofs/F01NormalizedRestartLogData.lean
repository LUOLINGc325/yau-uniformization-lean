import Yau.Proofs.F01NormalizedRestartProfile
import Yau.Proofs.F01NormalizedNativeSliceMatrix

/-! The actual restarted potential retains the original background's
positive matrix and logdet right-hand side in the same normalized chart. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem normalized_restart_log_data
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (W : M.Carrier → ℝ → ℝ)
    {σ ε r : ℝ} (hσ : 0 < σ) (hσr : σ ≤ A.radius) (hrε : σ ^ 2 * r ≤ ε)
    (T : ℝ) (hW : SmoothSpaceTime W (Icc 0 ε))
    (hpot : ∀ s ∈ Icc 0 ε, ∀ y,
      gMat (h s) y = gMat g y - ((T + s : ℝ) : ℂ) • ricci g y + levi (fun z => W z s) y)
    (a : M.Carrier) {p : Point n} (hp : p ∈ ball 0 1 ×ˢ Ico 0 r) :
    flowLogDetRatio g h (A.chart a (σ • p.1)) (σ ^ 2 * p.2) =
      localPotentialClockRHS (shiftedComplexBackground A a σ T)
        (fun q => normalizedPotentialLogSource A a σ q.1)
        (shiftedNativePotential A (absoluteRestartPotential W T) a σ T) p ∧
    (chartPotentialMatrix (shiftedComplexBackground A a σ T)
      (shiftedNativePotential A (absoluteRestartPotential W T) a σ T) p).PosDef := by
  have hClock : σ ^ 2 * p.2 ∈ Icc 0 ε :=
    ⟨mul_nonneg (sq_nonneg σ) hp.2.1,
      (mul_le_mul_of_nonneg_left hp.2.2.le (sq_nonneg σ)).trans hrε⟩
  have hSlice := smoothSpaceTime_slice hW hClock
  have hEq : (fun z => shiftedNativePotential A (absoluteRestartPotential W T) a σ T (z, p.2)) =
      (fun z => (σ ^ 2)⁻¹ * W (A.chart a (σ • z)) (σ ^ 2 * p.2)) :=
    funext (fun z => normalized_restart_profile_eq A W a σ T (z, p.2))
  have hMatrix : chartPotentialMatrix (shiftedComplexBackground A a σ T)
      (shiftedNativePotential A (absoluteRestartPotential W T) a σ T) p =
      pullbackMatrix (h (σ ^ 2 * p.2)) (A.chart a) (σ • p.1) := by
    change shiftedComplexBackground A a σ T p + leviC
      (fun z => shiftedNativePotential A (absoluteRestartPotential W T) a σ T (z, p.2)) p.1 = _
    rw [hEq]
    exact normalized_native_slice_matrix_at hg A (h (σ ^ 2 * p.2))
      (fun y => W y (σ ^ 2 * p.2)) hSlice hσ.ne' a p
      (spatialDilation_mem_ball hσ hσr hp.1) (hpot _ hClock)
  have hSource : σ • p.1 ∈ (A.chart a).source :=
    A.closedBall_source a (ball_subset_closedBall (spatialDilation_mem_ball hσ hσr hp.1))
  constructor
  · change flowLogDetRatio g h (A.chart a (σ • p.1)) (σ ^ 2 * p.2) =
      Real.log (chartPotentialMatrix (shiftedComplexBackground A a σ T)
        (shiftedNativePotential A (absoluteRestartPotential W T) a σ T) p).det.re +
        normalizedPotentialLogSource A a σ p.1
    rw [hMatrix]
    have hh := flowLogDetRatio_pullback_difference g h (A.chart a)
      (A.differentiable a) (A.inverse_differentiable a) hSource (σ ^ 2 * p.2)
    simpa only [normalizedPotentialLogSource, BoundedChartFamily.backgroundLogDet, sub_eq_add_neg] using hh
  · rw [hMatrix]
    exact pullbackMatrix_posDef _ (A.chart a) (A.differentiable a) (A.inverse_differentiable a) hSource

end Yau.NodeProofs.F01Aux
