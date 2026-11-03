import Yau.Proofs.V03AmbientBoundaryRegularity
import Yau.Proofs.V03ImmersionChartBound
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Actual local Lipschitz bounds for the cleared ambient tensor in the
immersion's ambient distance and physical time. The complete closed time
slabs are included in the bound, including both endpoints. -/

open scoped Topology ContDiff Manifold Matrix.Norms.Elementwise

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem fixedAmbientBoundaryTensor_local_lipschitz {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (x : Pt X) {z : CotangentCoord n}
    (hz : z ∈ cotangentTarget x) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ Metric.ball z r ⊆ cotangentTarget x ∧
      ∀ u ∈ Metric.ball z r, ∀ v ∈ Metric.ball z r,
      ∀ t ∈ Set.Icc 0 d.T, ∀ t' ∈ Set.Icc 0 d.T,
      ∀ s ∈ Set.Icc 0 d.T, ∀ s' ∈ Set.Icc 0 d.T,
        ‖fixedAmbientBoundaryTensor d j a x ((u, t), s) -
          fixedAmbientBoundaryTensor d j a x ((v, t'), s')‖ ≤
          C * (‖d.G (cotangentChartInv x u) - d.G (cotangentChartInv x v)‖ +
            |t - t'| + |s - s'|) := by
  obtain ⟨r, C₀, hr, hC₀, hrS, hlow⟩ := cotangentImmersion_local_chart_bound
    hd.2.2.2.2.1 x hz
  let S := ((Metric.closedBall z (r / 2) ×ˢ Set.Icc 0 d.T) ×ˢ Set.Icc 0 d.T)
  have hball : Metric.closedBall z (r / 2) ⊆ Metric.ball z r :=
    Metric.closedBall_subset_ball (half_lt_self hr)
  have hsub : S ⊆ ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ) := by
    intro p hp
    exact ⟨⟨hrS (hball hp.1.1), ⟨hp.1.2.1, hp.1.2.2.trans hd.2.1.le⟩⟩, Set.mem_univ _⟩
  have hB : ContDiffOn ℝ ∞ (fixedAmbientBoundaryTensor d j a x) S := by
    apply contDiffOn_pi.mpr
    intro b
    apply contDiffOn_pi.mpr
    intro c
    exact (fixedAmbientBoundaryTensor_entry_contDiffOn hd j a x b c).mono hsub
  obtain ⟨K, hK⟩ := hB.exists_lipschitzOnWith (by simp)
    (((convex_closedBall z (r / 2)).prod (convex_Icc 0 d.T)).prod (convex_Icc 0 d.T))
    (((isCompact_closedBall z (r / 2)).prod isCompact_Icc).prod isCompact_Icc)
  refine ⟨r / 2, (K : ℝ) * (C₀ + 1), half_pos hr,
    mul_nonneg K.2 (by linarith), ?_, ?_⟩
  · exact (Metric.ball_subset_ball (half_le_self hr.le)).trans hrS
  intro u hu v hv t ht t' ht' s hs s' hs'
  have hu' := Metric.ball_subset_closedBall hu
  have hv' := Metric.ball_subset_closedBall hv
  have hlu := hlow u (hball hu') v (hball hv')
  have hdist := hK.dist_le_mul ((u, t), s)
    (show ((u, t), s) ∈ S from ⟨⟨hu', ht⟩, hs⟩) ((v, t'), s')
    (show ((v, t'), s') ∈ S from ⟨⟨hv', ht'⟩, hs'⟩)
  have hmax : dist ((u, t), s) ((v, t'), s') ≤ ‖u - v‖ + |t - t'| + |s - s'| := by
    rw [Prod.dist_eq, Prod.dist_eq, dist_eq_norm u v, Real.dist_eq, Real.dist_eq]
    exact max_le (max_le (by linarith [abs_nonneg (t - t'), abs_nonneg (s - s')])
      (by linarith [norm_nonneg (u - v), abs_nonneg (s - s')]))
      (by linarith [norm_nonneg (u - v), abs_nonneg (t - t')])
  have hsum : ‖u - v‖ + |t - t'| + |s - s'| ≤
      (C₀ + 1) * (‖d.G (cotangentChartInv x u) - d.G (cotangentChartInv x v)‖ +
        |t - t'| + |s - s'|) := by
    nlinarith [norm_nonneg (d.G (cotangentChartInv x u) - d.G (cotangentChartInv x v)),
      abs_nonneg (t - t'), abs_nonneg (s - s')]
  rw [dist_eq_norm] at hdist
  simpa only [mul_assoc] using
    hdist.trans (mul_le_mul_of_nonneg_left (hmax.trans hsum) K.2)

end Yau.Blueprint.V03Proof
