import Yau.Proofs.V02WallTaylorOrdinaryJetDomain
import Yau.Proofs.V02WallTaylorUniformDomain

/-! Compact actual third-jet bounds for the nonsingular original boundary
cost, retaining both endpoints of the physical time slab. -/

open scoped Topology ContDiff Manifold
open Filter

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n q b : ℕ} {X : KahlerManifold n}

def ordinaryJetCompact (A : CotangentCoord n) (δ r C T : ℝ) : Set (ℂ × OrdinaryAux n b) :=
  Metric.closedBall (0 : ℂ) r ×ˢ
    ((Metric.closedBall A δ ×ˢ (Metric.closedBall (0 : ℂ) 1 ×ˢ Metric.closedBall (0 : Fin b → ℂ) C)) ×ˢ
      Set.Icc 0 T)

theorem isCompact_ordinaryJetCompact (A : CotangentCoord n) (δ r C T : ℝ) :
    IsCompact (ordinaryJetCompact (b := b) A δ r C T) :=
  (isCompact_closedBall _ _).prod (((isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod isCompact_Icc)

theorem ordinaryJetCompact_subset {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (x : Pt X) {A : CotangentCoord n} {δ R r C : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hC : 0 ≤ C)
    (hr : r < R / (2 * (C + 1)))
    (hsource : ∀ u ∈ Metric.closedBall A δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u), τ)).val ∈ cotangentSource x) :
    ordinaryJetCompact (b := b) A δ r C d.T ⊆ ordinaryJetDomain d j a Ψ x A δ R := by
  intro p hp
  have hz : ‖p.1‖ < R / (2 * (C + 1)) :=
    (show ‖p.1‖ ≤ r by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.1).trans_lt hr
  have hβ : ‖p.2.1.2.1‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2.1.2.1
  have hc : ‖p.2.1.2.2‖ ≤ C := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2.1.2.2
  have ht := norm_scaled_chartFactorDirection_lt (p := (p.1, p.2.1))
    (wallPower_mem_Icc hd j a (cotangentChartInv x p.2.1.1)) hC hβ hc hz
  refine ⟨⟨Set.mem_univ _, Set.mem_univ _, hp.2.2⟩, ?_⟩
  apply sprayScalar_domain_contains_closed_buffer hδ hR hsource
  exact ⟨hp.2.1.1, by simpa only [Metric.mem_closedBall, dist_zero_right, ordinarySprayCoordinate] using ht.le⟩

theorem exists_uniform_chart_ordinary_third_bound {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (x : Pt X) {A : CotangentCoord n} {δ R r C : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hC : 0 ≤ C)
    (hr : r < R / (2 * (C + 1)))
    (hvalid : Metric.ball A (2 * δ) ⊆ cotangentTarget x)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball A (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ u ∈ Metric.closedBall A δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u), τ)).val ∈ cotangentSource x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ ordinaryJetCompact (b := b) A δ r C d.T,
      ‖iteratedFDeriv ℝ 3 (fun z => ordinaryBoundaryScalar d j
        (nativeWallPoint d j a Ψ (cotangentChartInv x p.2.1.1) (z, p.2.1.2)) p.2.2) p.1‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_parameterJetWithin_bound
    (S := ordinaryJetDomain d j a Ψ x A δ R) (f := ordinaryJetFunction d j a Ψ x)
    (ordinaryJetDomain_uniqueDiffOn hd j a x hvalid hΨ)
    (ordinaryJetFunction_contDiffOn hd j a x hvalid hΨ)
    (fun p hp => ordinaryJetDomain_slice hd j a x hvalid hΨ hp)
    (isCompact_ordinaryJetCompact A δ r C d.T)
    (ordinaryJetCompact_subset hd j a x hδ hR hC hr hsource) 3
  refine ⟨B, hB, fun p hp => ?_⟩
  have hz : p.1 ∈ Metric.ball (0 : ℂ) (R / (2 * (C + 1))) :=
    Metric.closedBall_subset_ball hr hp.1
  have he : (fun z => ordinaryBoundaryScalar d j
      (nativeWallPoint d j a Ψ (cotangentChartInv x p.2.1.1) (z, p.2.1.2)) p.2.2) =ᶠ[𝓝 p.1]
      (fun z => ordinaryJetFunction d j a Ψ x (z, p.2)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with z hz'
    have hzn : ‖z‖ < R / (2 * (C + 1)) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz'
    have hβ : ‖p.2.1.2.1‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2.1.2.1
    have hc : ‖p.2.1.2.2‖ ≤ C := by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2.1.2.2
    have ht := norm_scaled_chartFactorDirection_lt (p := (z, p.2.1))
      (wallPower_mem_Icc hd j a (cotangentChartInv x p.2.1.1)) hC hβ hc hzn
    have hsrc := hsource _ hp.2.1.1 _
      (show wallPower d j a (cotangentChartInv x p.2.1.1) • chartFactorDirection (z, p.2.1) ∈
        Metric.closedBall (0 : Fin b → ℂ) (R / 2) from by
          simpa only [Metric.mem_closedBall, dist_zero_right] using ht.le)
    exact (sprayOrdinaryScalar_eq_actual d j (Ψ := Ψ) x
      (p := (ordinarySprayCoordinate d j a x (z, p.2), p.2.2)) hsrc).symm
  rw [(he.iteratedFDeriv (𝕜 := ℝ) 3).eq_of_nhds]
  exact hbound p hp

end Yau.Blueprint.V02WallTaylorProof
