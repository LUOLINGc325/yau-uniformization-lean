import Yau.Proofs.D02DistanceLipschitz

/-! Actual distance functions have genuine weak planar gradients bounded
by the original disc energy. The bound is independent of the target point. -/

open scoped Manifold Topology ContDiff NNReal
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem distanceFunction_lineDeriv_unit_bound (g : SmoothMetric M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) (p : M.Carrier)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (i : Fin 2) :
    ‖lineDeriv ℝ (fun w => lengthDist g.form (f w) p) z (if i = 0 then 1 else Complex.I)‖ ≤
      Real.sqrt (closedDiscDensity g.form f z) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro C hC
  have hC0 : 0 ≤ C := (Real.sqrt_nonneg _).trans hC.le
  have hn : closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
    mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall
  have hq : ContinuousAt (fun w => Real.sqrt (closedDiscDensity g.form f w)) z :=
    Real.continuous_sqrt.continuousAt.comp ((closedDiscDensity_continuousOn g hf).continuousAt hn)
  have hV : ball (0 : ℂ) 1 ∩ {w | Real.sqrt (closedDiscDensity g.form f w) < C} ∈ 𝓝 z :=
    inter_mem (isOpen_ball.mem_nhds hz) (hq.preimage_mem_nhds (Iio_mem_nhds hC))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hV
  have hLip := distanceFunction_lipschitzOn_of_density_bound g hf isOpen_ball (convex_ball z r)
    (fun w hw => (hsub hw).1) hC0 (fun w hw => (hsub hw).2.le) p
  have hd : ‖lineDeriv ℝ (fun w => lengthDist g.form (f w) p) z
      (if i = 0 then 1 else Complex.I)‖ ≤ C * ‖(if i = 0 then 1 else Complex.I : ℂ)‖ :=
    norm_lineDeriv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds (mem_ball_self hr)) hLip
  have he : ‖(if i = 0 then 1 else Complex.I : ℂ)‖ = 1 := by
    split_ifs <;> simp
  simpa only [he, mul_one] using hd

theorem distanceFunction_exists_actualWeakGradient (g : SmoothMetric M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) (p : M.Carrier) (z₀ : ℂ) (r : ℝ)
    (hdisc : closedBall z₀ r ⊆ ball (0 : ℂ) 1) :
    ∃ G : ℂ → LeafCandidates.RV 2,
      ContinuousOn (fun z => lengthDist g.form (f z) p) (ball z₀ r) ∧
      LeafCandidates.WeakPlanarGradient (ball z₀ r) (fun z => lengthDist g.form (f z) p) G ∧
      ∀ z ∈ ball z₀ r, ‖G z‖ ≤ Real.sqrt (2 * closedDiscDensity g.form f z) := by
  obtain ⟨C, hC⟩ := disc_distanceFunction_uniform_lipschitz g hf z₀ r hdisc
  obtain ⟨G, hG, hcoords⟩ := lipschitzOn_exists_weakPlanarGradient (hC p) isOpen_ball isBounded_ball
  refine ⟨G, (hC p).continuousOn, hG, fun z hz => ?_⟩
  have hzD := hdisc (ball_subset_closedBall hz)
  have h0 := distanceFunction_lineDeriv_unit_bound g hf p hzD (0 : Fin 2)
  have h1 := distanceFunction_lineDeriv_unit_bound g hf p hzD (1 : Fin 2)
  rw [← hcoords z hz 0] at h0
  rw [← hcoords z hz 1] at h1
  have hnorm := EuclideanSpace.norm_sq_eq (G z)
  simp only [Fin.sum_univ_two] at hnorm
  have hq := closedDiscDensity_nonneg g.form f z
  have hs := Real.sq_sqrt hq
  have hgs : ‖G z‖ ^ 2 ≤ 2 * closedDiscDensity g.form f z := by
    nlinarith [norm_nonneg (G z 0), norm_nonneg (G z 1), Real.sqrt_nonneg (closedDiscDensity g.form f z)]
  have htwo : 0 ≤ 2 * closedDiscDensity g.form f z := mul_nonneg (by norm_num) hq
  nlinarith [Real.sq_sqrt htwo, Real.sqrt_nonneg (2 * closedDiscDensity g.form f z), norm_nonneg (G z)]

end Yau.NodeProofs.D02Aux
