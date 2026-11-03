import Yau.Proofs.V02WallTaylorBoundaryCost
import Yau.Proofs.V02WallTaylorUniformLog

/-! A common parameter radius and actual uniform third-jet bounds for the
original boundaryCost and logarithmic Fourier energy of the native spray. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

theorem exists_uniform_spray_boundary_log_C3
    {n q b N : ℕ} {X : KahlerManifold n} {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a)
    {Ψ : V03Proof.NativeCotangentPoint X.manifold × (Fin b → ℂ) →
      V03Proof.NativeCotangentPoint X.manifold}
    {U : Set (V03Proof.NativeCotangentPoint X.manifold)}
    (hU : IsOpen U)
    (K : Set (CotangentPoint X.manifold)) (hK : CotangentCompact K)
    (hKU : ∀ y ∈ K, V03Proof.NativeCotangentPoint.mk y ∈ U)
    (x : Fin N → Pt X) (A : Fin N → CotangentCoord n)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hvalid : ∀ k, Metric.closedBall (A k) (8 * δ) ⊆ cotangentTarget (x k))
    (hcover : K ⊆ ⋃ k, cotangentChartInv (x k) '' Metric.ball (A k) δ)
    (hzero : ∀ y, Ψ (y, 0) = y)
    (hnative : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ Metric.ball 0 R))
    (hψ : ∀ k, ContDiffOn ℂ ∞ (sprayCoordinate Ψ (x k))
      (Metric.ball (A k) (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ k, ∀ u ∈ Metric.closedBall (A k) δ,
      ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (V03Proof.NativeCotangentPoint.mk (cotangentChartInv (x k) u), τ)).val ∈
        cotangentSource (x k))
    {E0 C0 D0 : ℝ} (hE0 : 0 ≤ E0) (hC0 : 0 ≤ C0) (hD0 : 0 ≤ D0) :
    ∃ r Mbc Mlog : ℝ, 0 < r ∧ r < R / (2 * (C0 + 1)) ∧ 0 ≤ Mbc ∧ 0 ≤ Mlog ∧
      ∀ F : VariationDisc X, AdmissibleVariationDisc d j F →
      (variationEnergy d j F).toReal ≤ E0 →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, F.f ζ ∈ K) →
      ∀ c : ℂ → Fin b → ℂ,
      (∀ k, ContDiffOn ℂ ∞ (fun ζ => c ζ k) (Metric.closedBall (0 : ℂ) 1)) →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ‖c ζ‖ ≤ C0) →
      boundaryDSq (fun θ k => c (circlePoint θ) k) ≤ ENNReal.ofReal D0 →
      (∀ z ∈ Metric.ball (0 : ℂ) r, ∀ θ : ℝ,
        wallSprayFamily d j a Ψ F c z (circlePoint θ) ∈ boundaryRegion d j) ∧
      (ContDiffOn ℝ 3 (fun z => boundaryCost d j {F with f := wallSprayFamily d j a Ψ F c z})
          (Metric.ball (0 : ℂ) r) ∧
        ∀ z ∈ Metric.ball (0 : ℂ) r,
          ‖iteratedFDeriv ℝ 3
            (fun p => boundaryCost d j {F with f := wallSprayFamily d j a Ψ F c p}) z‖ ≤ Mbc) ∧
      (ContDiffOn ℝ 3
          (fun z => (scalarDSq (logTrace d j (wallSprayFamily d j a Ψ F c z))).toReal)
          (Metric.ball (0 : ℂ) r) ∧
        ∀ z ∈ Metric.ball (0 : ℂ) r,
          ‖iteratedFDeriv ℝ 3
            (fun p => (scalarDSq (logTrace d j (wallSprayFamily d j a Ψ F c p))).toReal) z‖ ≤ Mlog) := by
  obtain ⟨rb, Mbc, hrb, hrbR, hMbc, hbc⟩ := exists_uniform_spray_boundaryCost_C3 hd j a
    (by omega : 3 ≤ a) K hK hKU x A hδ hR hC0 hvalid hcover hzero hnative hψ hsource
  obtain ⟨rl, Mlog, hrl, hrlR, hMlog, hlog⟩ := exists_uniform_spray_log_C3 hd j a
    (by omega : 3 ≤ a) hzero x A hδ hR hC0 hE0 hD0 hvalid hψ hsource hK hcover
  let r := min rb rl
  have hr : 0 < r := lt_min hrb hrl
  have hrR : r < R / (2 * (C0 + 1)) := (min_le_left _ _).trans_lt hrbR
  refine ⟨r, Mbc, Mlog, hr, hrR, hMbc, hMlog, fun F hF hE hFK c hc hcC hcD => ?_⟩
  have hbcF := hbc F hF hFK c hc hcC
  have hboundary : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ θ : ℝ,
      wallSprayFamily d j a Ψ F c z (circlePoint θ) ∈ boundaryRegion d j :=
    fun z hz => hbcF.1 z (Metric.ball_subset_ball (min_le_left _ _) hz)
  have hfamily := wallSprayFamily_holomorphicDiscFamily hd j a hR hr hC0 hrR.le hzero hnative hF
    (fun ζ hζ => hKU _ (hFK ζ hζ)) hc hcC
  refine ⟨hboundary, ?_, hlog r hr (min_le_right _ _) F hF hE hFK c hc hcC hcD hfamily hboundary⟩
  exact ⟨hbcF.2.1.mono (Metric.ball_subset_ball (min_le_left _ _)),
    fun z hz => hbcF.2.2 z (Metric.ball_subset_ball (min_le_left _ _) hz)⟩

end Yau.Blueprint.V02WallTaylorProof
