import Yau.Proofs.V02WallTaylorCompactIncrementJets

/-! Local regularity of the literal operator jets on one common compact
parameter tube, for use in the half-order trace composition theorem. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n q b : ℕ} {X : KahlerManifold n}

theorem nativeIncrementJet_contDiffAt_of_chart_domain {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 3 ≤ a)
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (hzero : ∀ y, Ψ (y, 0) = y) (x : Pt X)
    {A : CotangentCoord n} {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hvalid : Metric.ball A (2 * δ) ⊆ cotangentTarget x)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball A (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ u ∈ Metric.closedBall A δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u), τ)).val ∈ cotangentSource x)
    (m : ℕ) {y : CotangentPoint X.manifold} {p : IncrementAux b} (hy : y ∈ cotangentSource x)
    (hp : (p.1, (cotangentChart x y, p.2)) ∈ nativeIncrementDomain d j a Ψ x A δ R) :
    ContDiffAt ℝ 1 (fun w : CotangentCoord n × IncrementAux b =>
      nativeIncrementJet d j a Ψ m (cotangentChartInv y.1 w.1) w.2) (cotangentChart y.1 y, p) := by
  have hΩ := isOpen_nativeIncrementDomain hd j a hvalid hΨ
  have hsmooth := native_wall_increments_contDiffOn hd j a ha hzero x hδ hR hvalid hΨ hsource
  have hreal := intrinsicParameterJet_contDiffAt_chart hΩ hsmooth.1 m hp
  have hcomplex := intrinsicParameterJet_contDiffAt_chart
    (B := fun y p => (nativeLogIncrement d j a Ψ y p : ℂ)) (inv := cotangentChartInv x) hΩ
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hsmooth.2) m hp
  exact intrinsicCoefficient_contDiffAt_of_fixed_chart x hy (hreal.prodMk hcomplex)

theorem exists_uniform_native_increment_jet_local {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 3 ≤ a) {N : ℕ}
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (hzero : ∀ y, Ψ (y, 0) = y) (x : Fin N → Pt X) (A : Fin N → CotangentCoord n)
    {δ R C : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hC : 0 ≤ C)
    (hvalid : ∀ k, Metric.closedBall (A k) (8 * δ) ⊆ cotangentTarget (x k))
    (hΨ : ∀ k, ContDiffOn ℂ ∞ (sprayCoordinate Ψ (x k))
      (Metric.ball (A k) (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ k, ∀ u ∈ Metric.closedBall (A k) δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv (x k) u), τ)).val ∈ cotangentSource (x k))
    {K : Set (CotangentPoint X.manifold)}
    (hcover : K ⊆ ⋃ k, cotangentChartInv (x k) '' Metric.ball (A k) δ) :
    ∃ r : ℝ, 0 < r ∧ r < R / (2 * (C + 1)) ∧ ∀ m : ℕ,
      ∀ y ∈ K, ∀ p ∈ incrementAuxCompact b r C,
      ContDiffAt ℝ 1 (fun w : CotangentCoord n × IncrementAux b =>
        nativeIncrementJet d j a Ψ m (cotangentChartInv y.1 w.1) w.2) (cotangentChart y.1 y, p) := by
  classical
  have hval (k : Fin N) : Metric.ball (A k) (2 * δ) ⊆ cotangentTarget (x k) := by
    intro u hu
    exact hvalid k (Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hu))
  choose r hr hrR hrdomain using fun k =>
    exists_uniform_chart_increment_domain hd j a hzero (x k) hδ hR hC (hval k) (hΨ k) (hsource k)
  obtain ⟨t, ht, htR, htr⟩ := exists_pos_common_radius r hr
    (show 0 < R / (2 * (C + 1)) by positivity)
  refine ⟨t / 2, half_pos ht, (half_lt_self ht).trans htR, fun m y hy p hp => ?_⟩
  obtain ⟨k, u, hu, huy⟩ := Set.mem_iUnion.mp (hcover hy)
  have hz : p.1 ∈ Metric.ball (0 : ℂ) (r k) :=
    Metric.closedBall_subset_ball ((half_lt_self ht).trans_le (htr k)) hp.1
  have huT := hval k (Metric.ball_subset_ball (by linarith) hu)
  have hysrc : y ∈ cotangentSource (x k) := by rw [← huy]; exact cotangentChartInv_mapsTo _ huT
  have hcoord : cotangentChart (x k) y = u := by rw [← huy, cotangentChart_right_inv _ huT]
  apply nativeIncrementJet_contDiffAt_of_chart_domain hd j a ha hzero (x k) hδ hR
    (hval k) (hΨ k) (hsource k) m hysrc
  rw [hcoord]
  exact hrdomain k _ hz _ hu _ hp.2.1 _ hp.2.2

end Yau.Blueprint.V02WallTaylorProof
