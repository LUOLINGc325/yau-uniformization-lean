import Yau.Proofs.V02WallTaylorBoundaryCostBinding
import Yau.Proofs.V02WallTaylorOrdinaryBoundary
import Yau.Proofs.V02WallTaylorCompactIncrementJets

/-! A single radius and third-jet constant control the original boundaryCost
for every original admissible disc and bounded holomorphic coefficient vector. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n q b : ℕ} {X : KahlerManifold n}

theorem exists_uniform_spray_boundaryCost_C3 {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 3 ≤ a) {N : ℕ}
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    {U : Set (NativeCotangentPoint X.manifold)}
    (K : Set (CotangentPoint X.manifold)) (hK : CotangentCompact K)
    (hKU : ∀ y ∈ K, NativeCotangentPoint.mk y ∈ U)
    (x : Fin N → Pt X) (A : Fin N → CotangentCoord n)
    {δ R C : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hC : 0 ≤ C)
    (hvalid : ∀ k, Metric.closedBall (A k) (8 * δ) ⊆ cotangentTarget (x k))
    (hcover : K ⊆ ⋃ k, cotangentChartInv (x k) '' Metric.ball (A k) δ)
    (hzero : ∀ y, Ψ (y, 0) = y)
    (hnative : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ Metric.ball 0 R))
    (hψ : ∀ k, ContDiffOn ℂ ∞ (sprayCoordinate Ψ (x k))
      (Metric.ball (A k) (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ k, ∀ u ∈ Metric.closedBall (A k) δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv (x k) u), τ)).val ∈ cotangentSource (x k)) :
    ∃ r M : ℝ, 0 < r ∧ r < R / (2 * (C + 1)) ∧ 0 ≤ M ∧
      ∀ F : VariationDisc X, AdmissibleVariationDisc d j F →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, F.f ζ ∈ K) →
      ∀ c : ℂ → Fin b → ℂ,
      (∀ k, ContDiffOn ℂ ∞ (fun ζ => c ζ k) (Metric.closedBall (0 : ℂ) 1)) →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ‖c ζ‖ ≤ C) →
      (∀ z ∈ Metric.ball (0 : ℂ) r, ∀ θ,
        wallSprayFamily d j a Ψ F c z (circlePoint θ) ∈ boundaryRegion d j) ∧
      (ContDiffOn ℝ 3 (fun z => boundaryCost d j {F with f := wallSprayFamily d j a Ψ F c z})
          (Metric.ball (0 : ℂ) r) ∧
        ∀ z ∈ Metric.ball (0 : ℂ) r,
          ‖iteratedFDeriv ℝ 3 (fun p => boundaryCost d j {F with f := wallSprayFamily d j a Ψ F c p}) z‖ ≤ M) := by
  obtain ⟨ri, hri, hriR, hjet⟩ := exists_uniform_native_increment_jet_control hd j a ha hzero x A hδ hR hC hvalid hψ hsource hK hcover
  obtain ⟨L, B, _, hB, hsup, _⟩ := hjet 3
  obtain ⟨rp, hrp, hrpR, hpersist⟩ := exists_uniform_spray_boundary_region hd j a (by omega) hzero x A hδ hR hC hvalid hψ hsource K hcover
  let r := min ri rp
  have hr : 0 < r := lt_min hri hrp
  have hrR : r < R / (2 * (C + 1)) := (min_le_left _ _).trans_lt hriR
  obtain ⟨O, hO, hordinary⟩ := exists_uniform_ordinary_boundary_third_bound hd j a x A hδ hR hC hrR hvalid hψ hsource K hcover
  have hT : 0 < d.T := hd.1
  refine ⟨r, O + (1 + d.T) * B, hr, hrR, by positivity, fun F hF hFK c hc hcC => ?_⟩
  have hboundary : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ θ,
      wallSprayFamily d j a Ψ F c z (circlePoint θ) ∈ boundaryRegion d j :=
    fun z hz => hpersist F hF hFK c hcC z (Metric.ball_subset_ball (min_le_right _ _) hz)
  have hfamily := wallSprayFamily_holomorphicDiscFamily hd j a hR hr hC hrR.le hzero hnative hF
    (fun ζ hζ => hKU _ (hFK ζ hζ)) hc hcC
  refine ⟨hboundary, boundaryCost_C3_of_density_jets hd j a hF c hO hB hfamily hboundary
    (fun z hz => hordinary F hF hFK c hcC z (Metric.ball_subset_closedBall hz)) ?_⟩
  intro z hz θ
  let y := F.f (circlePoint θ)
  let p : IncrementAux b := (z, (outerWallPhase d j a F.f θ, c (circlePoint θ)))
  have hy : y ∈ K := hFK _ (circlePoint_mem_closedBall θ)
  have hp : p ∈ incrementAuxCompact b ri C := by
    refine ⟨Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_left _ _) hz), ?_, ?_⟩
    · simp only [p, Metric.mem_closedBall, dist_zero_right, outerWallPhase_norm, le_refl]
    · simpa only [p, Metric.mem_closedBall, dist_zero_right] using hcC _ (circlePoint_mem_closedBall θ)
  change ‖(nativeIncrementJet d j a Ψ 3 y p).1‖ ≤ B
  exact (show ‖(nativeIncrementJet d j a Ψ 3 y p).1‖ ≤ ‖nativeIncrementJet d j a Ψ 3 y p‖ from by
    rw [Prod.norm_def]; exact le_max_left _ _).trans (hsup _ hy _ hp)

end Yau.Blueprint.V02WallTaylorProof
