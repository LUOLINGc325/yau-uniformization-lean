import Yau.Proofs.D02RealDiscDifferential
import Yau.Proofs.D02WeakGradient

/-! Genuine length-distance Lipschitz estimates follow from the actual
disc derivative. Their constants are independent of the target point used
in a scalar distance function. -/

open scoped Manifold Topology ContDiff NNReal
open Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem disc_distance_le_of_density_bound (g : SmoothMetric M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f)
    {D : Set ℂ} (hD : IsOpen D) (hconv : Convex ℝ D) (hDdisc : D ⊆ ball (0 : ℂ) 1)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z ∈ D, Real.sqrt (closedDiscDensity g.form f z) ≤ C) :
    ∀ z ∈ D, ∀ w ∈ D, lengthDist g.form (f z) (f w) ≤ C * dist z w := by
  letI := L12Aux.manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => L12Aux.underlyingRealTangentNormedAddCommGroup g.form y
  apply L12Aux.inducedDistance_le_of_chart_deriv g f hD hconv hC
  · intro z hz
    exact (holomorphicDisc_contMDiffAt_real hf (hDdisc hz)).contMDiffWithinAt
  · intro z hz v
    rw [realDiscDerivative_norm g.form hf (hDdisc hz) v]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbound z hz) (norm_nonneg v)

theorem distanceFunction_lipschitzOn_of_density_bound (g : SmoothMetric M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f)
    {D : Set ℂ} (hD : IsOpen D) (hconv : Convex ℝ D) (hDdisc : D ⊆ ball (0 : ℂ) 1)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z ∈ D, Real.sqrt (closedDiscDensity g.form f z) ≤ C)
    (p : M.Carrier) :
    LipschitzOnWith ⟨C, hC⟩ (fun z => lengthDist g.form (f z) p) D := by
  letI := L12Aux.inducedMetricSpace g
  have hdist := disc_distance_le_of_density_bound g hf hD hconv hDdisc hC hbound
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  change dist (dist (f z) p) (dist (f w) p) ≤ C * dist z w
  exact (dist_dist_dist_le_left (f z) (f w) p).trans (hdist z hz w hw)

/-- The common scalar Lipschitz constant is selected before the arbitrary
target point p; only the actual derivative density enters it. -/
theorem disc_distanceFunction_uniform_lipschitz (g : SmoothMetric M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) (z₀ : ℂ) (r : ℝ)
    (hdisc : closedBall z₀ r ⊆ ball (0 : ℂ) 1) :
    ∃ C : ℝ≥0, ∀ p : M.Carrier,
      LipschitzOnWith C (fun z => lengthDist g.form (f z) p) (ball z₀ r) := by
  have hq : ContinuousOn (fun z => Real.sqrt (closedDiscDensity g.form f z)) (closedBall z₀ r) :=
    Real.continuous_sqrt.comp_continuousOn ((closedDiscDensity_continuousOn g hf).mono
      (hdisc.trans ball_subset_closedBall))
  obtain ⟨B, hB⟩ := (isCompact_closedBall z₀ r).bddAbove_image hq
  let C : ℝ≥0 := ⟨max B 0, le_max_right B 0⟩
  refine ⟨C, fun p => distanceFunction_lipschitzOn_of_density_bound g hf isOpen_ball
    (convex_ball z₀ r) (ball_subset_closedBall.trans hdisc) C.coe_nonneg ?_ p⟩
  intro z hz
  exact (hB (Set.mem_image_of_mem (fun z => Real.sqrt (closedDiscDensity g.form f z))
    (ball_subset_closedBall hz))).trans (le_max_left B 0)

end Yau.NodeProofs.D02Aux
