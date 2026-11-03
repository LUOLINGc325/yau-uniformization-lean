import Yau.Proofs.V02WallTaylorOrdinaryCompact
import Yau.Proofs.V02WallTaylorTraceIncrement

/-! The compact chart bound controls the actual nonsingular boundary density
for all original discs and coefficients before they are chosen. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n q b : ℕ} {X : KahlerManifold n}

theorem exists_uniform_ordinary_boundary_third_bound {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) {N : ℕ}
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (x : Fin N → Pt X) (A : Fin N → CotangentCoord n)
    {δ R r C : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hC : 0 ≤ C)
    (hr : r < R / (2 * (C + 1)))
    (hvalid : ∀ k, Metric.closedBall (A k) (8 * δ) ⊆ cotangentTarget (x k))
    (hΨ : ∀ k, ContDiffOn ℂ ∞ (sprayCoordinate Ψ (x k))
      (Metric.ball (A k) (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ k, ∀ u ∈ Metric.closedBall (A k) δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv (x k) u), τ)).val ∈ cotangentSource (x k))
    (K : Set (CotangentPoint X.manifold))
    (hcover : K ⊆ ⋃ k, cotangentChartInv (x k) '' Metric.ball (A k) δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ F : VariationDisc X, AdmissibleVariationDisc d j F →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, F.f ζ ∈ K) →
      ∀ c : ℂ → Fin b → ℂ, (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ‖c ζ‖ ≤ C) →
      ∀ z ∈ Metric.closedBall (0 : ℂ) r, ∀ θ : ℝ,
      ‖iteratedFDeriv ℝ 3 (fun p => ordinaryBoundaryScalar d j
        (wallSprayFamily d j a Ψ F c p (circlePoint θ)) (discTime F (circlePoint θ))) z‖ ≤ B := by
  classical
  have hval (k : Fin N) : Metric.ball (A k) (2 * δ) ⊆ cotangentTarget (x k) := by
    intro u hu
    exact hvalid k (Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hu))
  choose B hB hbound using fun k => exists_uniform_chart_ordinary_third_bound hd j a (x k)
    hδ hR hC hr (hval k) (hΨ k) (hsource k)
  refine ⟨∑ k, B k, Finset.sum_nonneg (fun k _ => hB k), fun F hF hFK c hc z hz θ => ?_⟩
  obtain ⟨k, u, hu, huy⟩ := Set.mem_iUnion.mp (hcover (hFK _ (circlePoint_mem_closedBall θ)))
  let β := outerWallPhase d j a F.f θ
  let cθ := c (circlePoint θ)
  let t := discTime F (circlePoint θ)
  let p : ℂ × OrdinaryAux n b := (z, ((u, (β, cθ)), t))
  have hp : p ∈ ordinaryJetCompact (b := b) (A k) δ r C d.T := by
    refine ⟨hz, ⟨Metric.ball_subset_closedBall hu, ?_, ?_⟩, ?_⟩
    · simp only [p, β, Metric.mem_closedBall, dist_zero_right, outerWallPhase_norm, le_refl]
    · simpa only [p, cθ, Metric.mem_closedBall, dist_zero_right] using hc _ (circlePoint_mem_closedBall θ)
    · have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
      exact ⟨ht.1.le, ht.2.le⟩
  have hh := hbound k p hp
  have heq : (fun w : ℂ => ordinaryBoundaryScalar d j
      (wallSprayFamily d j a Ψ F c w (circlePoint θ)) t) =
      (fun w : ℂ => ordinaryBoundaryScalar d j
        (nativeWallPoint d j a Ψ (cotangentChartInv (x k) u) (w, (β, cθ))) t) := by
    funext w
    rw [wallSprayFamily_boundary_eq_nativeWallPoint hd j a hF c w θ, huy]
  rw [heq]
  exact hh.trans (Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ k))

end Yau.Blueprint.V02WallTaylorProof
