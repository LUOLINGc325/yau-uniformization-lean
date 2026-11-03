import Yau.Proofs.V03AtlasCompact
import Yau.Proofs.V03ImmersionChartBound

/-! On an actual intrinsic compact set, ambient closeness under the
original injective immersion implies closeness in any valid cotangent
chart. This uses only the native compact embedding, not global properness. -/

open scoped Topology ContDiff Manifold
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}

theorem compact_cotangent_chart_neighborhood
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {K : Set (CotangentPoint M)} (hK : CotangentCompact K)
    {y : CotangentPoint M} (hyK : y ∈ K) (x : M.Carrier)
    (hy : y ∈ cotangentSource x) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ K, ‖G y' - G y‖ < δ →
      y' ∈ cotangentSource x ∧
        cotangentChart x y' ∈ Metric.ball (cotangentChart x y) r := by
  let S := NativeCotangentPoint.mk '' K
  let p : S := ⟨⟨y⟩, ⟨y, hyK, rfl⟩⟩
  let e := nativeCotangentChartHomeomorph x
  have hp : p.1 ∈ e.source := hy
  have hsource : ∀ᶠ p' : S in 𝓝 p, p'.1 ∈ e.source :=
    continuous_subtype_val.continuousAt.eventually (e.open_source.mem_nhds hp)
  have hcoord : ∀ᶠ p' : S in 𝓝 p, e p'.1 ∈ Metric.ball (e p.1) r :=
    ((e.continuousAt hp).comp continuous_subtype_val.continuousAt).eventually
      (Metric.ball_mem_nhds _ hr)
  have hnear := hsource.and hcoord
  rw [(cotangentImmersion_compact_isClosedEmbedding hG hK).isEmbedding.isInducing.nhds_eq_comap p]
    at hnear
  obtain ⟨V, hV, hVP⟩ := Filter.mem_comap.mp hnear
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨δ, hδ, fun y' hy' hdist => ?_⟩
  let p' : S := ⟨⟨y'⟩, ⟨y', hy', rfl⟩⟩
  have hmem : G y' ∈ Metric.ball (G y) δ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hdist
  exact hVP (hδV hmem : G p'.1.val ∈ V)

end Yau.Blueprint.V03Proof
