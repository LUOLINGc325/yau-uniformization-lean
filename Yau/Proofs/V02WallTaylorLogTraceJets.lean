import Yau.Proofs.V02WallTaylorLocalIncrementJets
import Yau.Proofs.V02WallTaylorAugmentedTrace
import Yau.Proofs.V02WallTaylorTraceBudget

/-! Actual logarithmic increment jets have uniform original half-order
bounds on every admissible boundary trace in the fixed energy class. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n q b : ℕ} {X : KahlerManifold n}

theorem exists_uniform_native_log_trace_jets {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 3 ≤ a) {N : ℕ}
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (hzero : ∀ y, Ψ (y, 0) = y) (x : Fin N → Pt X) (A : Fin N → CotangentCoord n)
    {δ R C0 E0 D0 : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hC0 : 0 ≤ C0)
    (hE0 : 0 ≤ E0) (hD0 : 0 ≤ D0)
    (hvalid : ∀ k, Metric.closedBall (A k) (8 * δ) ⊆ cotangentTarget (x k))
    (hΨ : ∀ k, ContDiffOn ℂ ∞ (sprayCoordinate Ψ (x k))
      (Metric.ball (A k) (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ k, ∀ u ∈ Metric.closedBall (A k) δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv (x k) u), τ)).val ∈ cotangentSource (x k))
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K)
    (hcover : K ⊆ ⋃ k, cotangentChartInv (x k) '' Metric.ball (A k) δ) :
    ∃ r : ℝ, 0 < r ∧ r < R / (2 * (C0 + 1)) ∧ ∀ m : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ F : VariationDisc X, AdmissibleVariationDisc d j F →
      (variationEnergy d j F).toReal ≤ E0 →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, F.f ζ ∈ K) →
      ∀ c : ℂ → Fin b → ℂ,
      (∀ k, ContDiffOn ℂ ∞ (fun ζ => c ζ k) (Metric.closedBall (0 : ℂ) 1)) →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ‖c ζ‖ ≤ C0) →
      boundaryDSq (fun θ k => c (circlePoint θ) k) ≤ ENNReal.ofReal D0 →
      ∀ z ∈ Metric.closedBall (0 : ℂ) r, ∀ v : Fin m → ℂ,
      boundaryDSq (fun θ (_ : Unit) =>
        (nativeIncrementJet d j a Ψ m (F.f (circlePoint θ))
          (z, (outerWallPhase d j a F.f θ, c (circlePoint θ)))).2 v) ≤
        ENNReal.ofReal ((B * ∏ i, ‖v i‖) ^ 2) := by
  obtain ⟨r, hr, hrR, hlocal⟩ := exists_uniform_native_increment_jet_local hd j a ha hzero x A hδ hR hC0 hvalid hΨ hsource hcover
  refine ⟨r, hr, hrR, fun m => ?_⟩
  let L : Set (EuclideanSpace ℂ (IncrementAuxIndex b)) := incrementAuxEncode '' incrementAuxCompact b r C0
  have hL : IsCompact L := (isCompact_incrementAuxCompact r C0).image incrementAuxEncode_contDiff.continuous
  let Bm : CotangentPoint X.manifold → EuclideanSpace ℂ (IncrementAuxIndex b) → ℂ [×m]→L[ℝ] ℂ :=
    fun y p => (nativeIncrementJet d j a Ψ m y (incrementAuxDecode p)).2
  have hBm : ∀ y ∈ K, ∀ p ∈ L,
      ContDiffAt ℝ 1 (fun w : CotangentCoord n × EuclideanSpace ℂ (IncrementAuxIndex b) =>
        Bm (cotangentChartInv y.1 w.1) w.2) (cotangentChart y.1 y, p) := by
    intro y hy p hp
    obtain ⟨p', hp', rfl⟩ := hp
    have hT : ContDiff ℝ ∞ (fun w : CotangentCoord n × EuclideanSpace ℂ (IncrementAuxIndex b) =>
        (w.1, incrementAuxDecode w.2)) :=
      contDiff_fst.prodMk (incrementAuxDecode_contDiff.comp contDiff_snd)
    exact (hlocal m y hy p' hp').snd.comp
      (f := fun w : CotangentCoord n × EuclideanSpace ℂ (IncrementAuxIndex b) => (w.1, incrementAuxDecode w.2))
      (cotangentChart y.1 y, incrementAuxEncode p') (hT.contDiffAt.of_le (by simp))
  obtain ⟨C, D, hC, _, hbound⟩ := augmentedJet_uniform_boundary_control hd.2.2.2.2.1 hK hL m hBm
  let S := combinedTraceBudget a E0 D0
  have hS : 0 ≤ S := combinedTraceBudget_nonneg a hE0 hD0
  refine ⟨Real.sqrt (C * S), Real.sqrt_nonneg _, fun F hF hE hFK c hc hcC hcD z hz v => ?_⟩
  let p : ℝ → EuclideanSpace ℂ (IncrementAuxIndex b) :=
    fun θ => incrementAuxEncode (z, (outerWallPhase d j a F.f θ, c (circlePoint θ)))
  have hp : ∀ θ, p θ ∈ L := by
    intro θ
    refine ⟨(z, (outerWallPhase d j a F.f θ, c (circlePoint θ))), ⟨hz, ?_, ?_⟩, rfl⟩
    · simp only [Metric.mem_closedBall, dist_zero_right, outerWallPhase_norm, le_refl]
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hcC _ (circlePoint_mem_closedBall θ)
  have hGc := admissible_ambient_trace_continuous hd hF
  have hpc : Continuous p := actual_aux_encode_continuous hd hF a z hc
  have hGp := circleTrace_periodic (fun ζ => d.G (F.f ζ))
  have hpp : Function.Periodic p (2 * Real.pi) := actual_aux_encode_periodic d j a F c z
  have hh := (hbound (fun θ => F.f (circlePoint θ))
    (fun θ => hFK _ (circlePoint_mem_closedBall θ)) p hp hGc hpc hGp hpp).2 v
  change boundaryDSq (fun θ (_ : Unit) =>
      (nativeIncrementJet d j a Ψ m (F.f (circlePoint θ))
        (z, (outerWallPhase d j a F.f θ, c (circlePoint θ)))).2 v) ≤
      ENNReal.ofReal (C * (∏ i, ‖v i‖) ^ 2) *
        (boundaryDSq (fun θ k => d.G (F.f (circlePoint θ)) k) + boundaryDSq (fun θ i => p θ i)) at hh
  calc
    _ ≤ ENNReal.ofReal (C * (∏ i, ‖v i‖) ^ 2) *
        (boundaryDSq (fun θ k => d.G (F.f (circlePoint θ)) k) + boundaryDSq (fun θ i => p θ i)) := hh
    _ ≤ ENNReal.ofReal (C * (∏ i, ‖v i‖) ^ 2) * ENNReal.ofReal S := by
      gcongr
      exact actual_combined_trace_budget hd j a hF hE0 hD0 hE hcD z
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hC (sq_nonneg _)), mul_pow,
        Real.sq_sqrt (mul_nonneg hC hS)]
      congr 1
      ring

end Yau.Blueprint.V02WallTaylorProof
