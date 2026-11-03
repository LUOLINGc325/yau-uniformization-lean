import Yau.Proofs.V02WallTaylorLogTraceJets
import Yau.Proofs.V02WallTaylorLogBinding

/-! One scalar third-jet constant controls the original logarithmic Fourier
energy on every smaller actual holomorphic boundary-preserving parameter disc. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n q b : ℕ} {X : KahlerManifold n}

theorem exists_uniform_spray_log_C3 {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 3 ≤ a) {N : ℕ}
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (hzero : ∀ y, Ψ (y, 0) = y) (x : Fin N → Pt X) (A : Fin N → CotangentCoord n)
    {δ R C0 E0 D0 : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hC0 : 0 ≤ C0) (hE0 : 0 ≤ E0) (hD0 : 0 ≤ D0)
    (hvalid : ∀ k, Metric.closedBall (A k) (8 * δ) ⊆ cotangentTarget (x k))
    (hΨ : ∀ k, ContDiffOn ℂ ∞ (sprayCoordinate Ψ (x k))
      (Metric.ball (A k) (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ k, ∀ u ∈ Metric.closedBall (A k) δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv (x k) u), τ)).val ∈ cotangentSource (x k))
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K)
    (hcover : K ⊆ ⋃ k, cotangentChartInv (x k) '' Metric.ball (A k) δ) :
    ∃ r M : ℝ, 0 < r ∧ r < R / (2 * (C0 + 1)) ∧ 0 ≤ M ∧
      ∀ s : ℝ, 0 < s → s ≤ r →
      ∀ F : VariationDisc X, AdmissibleVariationDisc d j F →
      (variationEnergy d j F).toReal ≤ E0 →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, F.f ζ ∈ K) →
      ∀ c : ℂ → Fin b → ℂ,
      (∀ k, ContDiffOn ℂ ∞ (fun ζ => c ζ k) (Metric.closedBall (0 : ℂ) 1)) →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ‖c ζ‖ ≤ C0) →
      boundaryDSq (fun θ k => c (circlePoint θ) k) ≤ ENNReal.ofReal D0 →
      HolomorphicDiscFamily F (wallSprayFamily d j a Ψ F c) s →
      (∀ z ∈ Metric.ball (0 : ℂ) s, ∀ θ,
        wallSprayFamily d j a Ψ F c z (circlePoint θ) ∈ boundaryRegion d j) →
      ContDiffOn ℝ 3
        (fun z => (scalarDSq (logTrace d j (wallSprayFamily d j a Ψ F c z))).toReal)
        (Metric.ball (0 : ℂ) s) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) s,
        ‖iteratedFDeriv ℝ 3
          (fun p => (scalarDSq (logTrace d j (wallSprayFamily d j a Ψ F c p))).toReal) z‖ ≤ M := by
  classical
  obtain ⟨r, hr, hrR, htrace⟩ := exists_uniform_native_log_trace_jets hd j a ha hzero x A hδ hR hC0 hE0 hD0 hvalid hΨ hsource hK hcover
  choose B hB hbudget using fun i : Fin 4 => htrace i
  let D := ∑ i, B i
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ => hB i)
  have hBD (i : Fin 4) : B i ≤ D := Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ i)
  refine ⟨r, 2 * (Real.sqrt E0 + D) * D + 6 * D ^ 2, hr, hrR, by positivity, ?_⟩
  intro s hs hsr F hF hE hFK c hc hcC hcD hfamily hboundary
  apply logEnergy_C3_of_increment_jets hd j a hzero hF c hs hE0 hD hD hE hfamily hboundary
  · intro z hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) r :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball hsr hz)
    have hb := hbudget (0 : Fin 4) F hF hE hFK c hc hcC hcD z hz' (fun i : Fin 0 => Fin.elim0 i)
    have hb' : boundaryDSq (fun θ (_ : Unit) => (nativeLogIncrement d j a Ψ (F.f (circlePoint θ))
        (z, (outerWallPhase d j a F.f θ, c (circlePoint θ))) : ℂ)) ≤ ENNReal.ofReal ((B (0 : Fin 4)) ^ 2) := by
      simpa [nativeIncrementJet, intrinsicParameterJet] using hb
    exact hb'.trans (ENNReal.ofReal_le_ofReal (by nlinarith [hBD (0 : Fin 4), hB (0 : Fin 4)]))
  · intro z hz m hm hm3 v
    have hz' : z ∈ Metric.closedBall (0 : ℂ) r :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball hsr hz)
    let i : Fin 4 := ⟨m, by omega⟩
    have hb := hbudget i F hF hE hFK c hc hcC hcD z hz' v
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    have hprod : 0 ≤ ∏ k, ‖v k‖ := Finset.prod_nonneg (fun k _ => norm_nonneg _)
    exact (sq_le_sq₀ (mul_nonneg (hB i) hprod) (mul_nonneg hD hprod)).mpr
      (mul_le_mul_of_nonneg_right (hBD i) hprod)

end Yau.Blueprint.V02WallTaylorProof
