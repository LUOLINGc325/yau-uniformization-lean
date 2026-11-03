import Yau.Proofs.V02FlowCoordinates
import Yau.Proofs.V03NativeMaps
import Yau.Proofs.V02WallTaylorTraceIncrement
import Yau.Proofs.V02WallTaylorBoundaryRegularity

/-! The literal family is jointly holomorphic by the actual native spray,
with the actual original outer candidate and original closed-disc data. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof

variable {n q b : ℕ} {X : KahlerManifold n}

theorem wallSprayFamily_holomorphicDiscFamily {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ)
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    {U : Set (NativeCotangentPoint X.manifold)} {R r C : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hC : 0 ≤ C) (hrR : r ≤ R / (2 * (C + 1)))
    (hzero : ∀ y, Ψ (y, 0) = y)
    (hΨ : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ Metric.ball 0 R))
    {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    (hFU : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, NativeCotangentPoint.mk (F.f ζ) ∈ U)
    {c : ℂ → Fin b → ℂ}
    (hc : ∀ k, ContDiffOn ℂ ∞ (fun ζ => c ζ k) (Metric.closedBall (0 : ℂ) 1))
    (hcC : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ‖c ζ‖ ≤ C) :
    HolomorphicDiscFamily F (wallSprayFamily d j a Ψ F c) r := by
  refine ⟨hr, wallSprayFamily_zero d j a hzero F c, ?_⟩
  let S := Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1
  let h := outerCandidate (logTrace d j F.f) a
  have hh : ContDiffOn ℂ ∞ h (Metric.closedBall (0 : ℂ) 1) :=
    outerCandidate_contDiffOn (admissible_logTrace_contDiff hd hF) (logTrace_periodic d j F) a
  have hsnd : ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) ∞ (Prod.snd : ℂ × ℂ → ℂ) S :=
    (contDiff_snd : ContDiff ℂ ∞ (Prod.snd : ℂ × ℂ → ℂ)).contMDiff.contMDiffOn
  have hFn : ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CotangentCoord n) ∞
      (fun p : ℂ × ℂ => NativeCotangentPoint.mk (F.f p.2)) S :=
    (cotangentDisc_native_contMDiffOn hF.1).comp hsnd (fun p hp => hp.2)
  have hτ : ContDiffOn ℂ ∞ (fun p : ℂ × ℂ => fun k => p.1 * h p.2 * c p.2 k) S := by
    apply contDiffOn_pi.mpr
    intro k
    exact (contDiffOn_fst.mul (hh.comp contDiffOn_snd (fun _ hp => hp.2))).mul
      ((hc k).comp contDiffOn_snd (fun _ hp => hp.2))
  have hparam (p : ℂ × ℂ) (hp : p ∈ S) :
      (fun k => p.1 * h p.2 * c p.2 k) ∈ Metric.ball (0 : Fin b → ℂ) R := by
    have hz : ‖p.1‖ < R / (2 * (C + 1)) :=
      (show ‖p.1‖ < r by simpa only [Metric.mem_ball, dist_zero_right] using hp.1).trans_le hrR
    have hhn : ‖h p.2‖ ≤ 1 := actual_outer_norm_le_one hd hF a hp.2
    have hn : ‖(fun k => p.1 * h p.2 * c p.2 k)‖ ≤ ‖p.1‖ * C := by
      change ‖(p.1 * h p.2) • c p.2‖ ≤ _
      rw [norm_smul, norm_mul]
      have hh' := mul_le_mul_of_nonneg_left hhn (norm_nonneg p.1)
      exact (mul_le_mul hh' (hcC _ hp.2) (norm_nonneg _) (by positivity)).trans_eq (by ring)
    rw [Metric.mem_ball, dist_zero_right]
    have hz' := (lt_div_iff₀ (show 0 < 2 * (C + 1) by positivity)).mp hz
    nlinarith [norm_nonneg p.1]
  exact V02FlowProof.native_contMDiffOn_cotangentHolomorphicOn
    (hΨ.comp (hFn.prodMk hτ.contMDiffOn) (fun p hp => ⟨hFU _ hp.2, hparam p hp⟩))

end Yau.Blueprint.V02WallTaylorProof
