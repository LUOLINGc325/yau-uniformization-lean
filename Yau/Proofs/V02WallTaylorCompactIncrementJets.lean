import Yau.Proofs.V02WallTaylorUniformDomain
import Yau.Proofs.V02WallTaylorIntrinsicJets
import Yau.Proofs.V02WallTaylorChartTransfer
import Yau.Proofs.V02WallTaylorCompactCoefficient

/-! Uniform bounds and actual immersion-distance Lipschitz control of every
literal reciprocal/log increment operator jet, before any disc or coefficient trace. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n q b : ℕ} {X : KahlerManifold n}

abbrev IncrementAux (b : ℕ) := ℂ × (ℂ × (Fin b → ℂ))

def incrementAuxCompact (b : ℕ) (r C : ℝ) : Set (IncrementAux b) :=
  Metric.closedBall (0 : ℂ) r ×ˢ
    (Metric.closedBall (0 : ℂ) 1 ×ˢ Metric.closedBall (0 : Fin b → ℂ) C)

theorem isCompact_incrementAuxCompact (r C : ℝ) : IsCompact (incrementAuxCompact b r C) :=
  (isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))

def nativeIncrementJet (d : VariationData X q) (j a : ℕ)
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (m : ℕ) (y : CotangentPoint X.manifold) (p : IncrementAux b) :
    (ℂ [×m]→L[ℝ] ℝ) × (ℂ [×m]→L[ℝ] ℂ) :=
  (intrinsicParameterJet (nativeInverseIncrement d j a Ψ) m y p,
    intrinsicParameterJet (fun y p => (nativeLogIncrement d j a Ψ y p : ℂ)) m y p)

theorem exists_uniform_native_increment_jet_control {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 3 ≤ a) {N : ℕ}
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (hzero : ∀ y, Ψ (y, 0) = y) (x : Fin N → Pt X) (A : Fin N → CotangentCoord n)
    {δ R C : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hC : 0 ≤ C)
    (hvalid : ∀ k, Metric.closedBall (A k) (8 * δ) ⊆ cotangentTarget (x k))
    (hΨ : ∀ k, ContDiffOn ℂ ∞ (sprayCoordinate Ψ (x k))
      (Metric.ball (A k) (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ k, ∀ u ∈ Metric.closedBall (A k) δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv (x k) u), τ)).val ∈ cotangentSource (x k))
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K)
    (hcover : K ⊆ ⋃ k, cotangentChartInv (x k) '' Metric.ball (A k) δ) :
    ∃ r : ℝ, 0 < r ∧ r < R / (2 * (C + 1)) ∧ ∀ m : ℕ,
      ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧
      (∀ y ∈ K, ∀ p ∈ incrementAuxCompact b r C, ‖nativeIncrementJet d j a Ψ m y p‖ ≤ B) ∧
      ∀ y ∈ K, ∀ y' ∈ K, ∀ p ∈ incrementAuxCompact b r C, ∀ p' ∈ incrementAuxCompact b r C,
      ‖nativeIncrementJet d j a Ψ m y p - nativeIncrementJet d j a Ψ m y' p'‖ ≤
        L * (‖d.G y - d.G y'‖ + ‖p - p'‖) := by
  classical
  have hval (k : Fin N) : Metric.ball (A k) (2 * δ) ⊆ cotangentTarget (x k) := by
    intro u hu
    exact hvalid k (Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hu))
  choose r hr hrR hrdomain using fun k =>
    exists_uniform_chart_increment_domain hd j a hzero (x k) hδ hR hC (hval k) (hΨ k) (hsource k)
  obtain ⟨t, ht, htR, htr⟩ := exists_pos_common_radius r hr
    (show 0 < R / (2 * (C + 1)) by positivity)
  refine ⟨t / 2, half_pos ht, (half_lt_self ht).trans htR, fun m => ?_⟩
  apply augmentedCoefficient_compact_control hd.2.2.2.2.1 hK (isCompact_incrementAuxCompact (t / 2) C)
  intro y hy p hp
  obtain ⟨k, u, hu, huy⟩ := Set.mem_iUnion.mp (hcover hy)
  have hz : p.1 ∈ Metric.ball (0 : ℂ) (r k) :=
    Metric.closedBall_subset_ball ((half_lt_self ht).trans_le (htr k)) hp.1
  have hDom : (p.1, (u, p.2)) ∈ nativeIncrementDomain d j a Ψ (x k) (A k) δ R :=
    hrdomain k _ hz _ hu _ hp.2.1 _ hp.2.2
  have hΩ := isOpen_nativeIncrementDomain hd j a (hval k) (hΨ k)
  have hsmooth := native_wall_increments_contDiffOn hd j a ha hzero (x k) hδ hR (hval k) (hΨ k) (hsource k)
  have hreal := intrinsicParameterJet_contDiffAt_chart hΩ hsmooth.1 m hDom
  have hcomplex := intrinsicParameterJet_contDiffAt_chart
    (B := fun y p => (nativeLogIncrement d j a Ψ y p : ℂ))
    (inv := cotangentChartInv (x k)) hΩ
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hsmooth.2) m hDom
  have hpair : ContDiffAt ℝ 1 (fun w : CotangentCoord n × IncrementAux b =>
      nativeIncrementJet d j a Ψ m (cotangentChartInv (x k) w.1) w.2) (u, p) :=
    hreal.prodMk hcomplex
  have huT := hval k (Metric.ball_subset_ball (by linarith) hu)
  have hysrc : y ∈ cotangentSource (x k) := by
    rw [← huy]
    exact cotangentChartInv_mapsTo _ huT
  have hcoord : cotangentChart (x k) y = u := by rw [← huy, cotangentChart_right_inv _ huT]
  apply intrinsicCoefficient_contDiffAt_of_fixed_chart (x k) hysrc
  simpa only [hcoord] using hpair

end Yau.Blueprint.V02WallTaylorProof
