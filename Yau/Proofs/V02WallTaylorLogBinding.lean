import Yau.Proofs.V02WallTaylorLogEnergy
import Yau.Proofs.V02WallTaylorCompactIncrementJets
import Yau.Proofs.V02WallTaylorFamily

/-! The original logarithmic Fourier energy is controlled by the actual
initial energy and cleared native increment jets; the mean is unrestricted. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n q b : ℕ} {X : KahlerManifold n}

theorem logEnergy_C3_of_increment_jets {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (hzero : ∀ y, Ψ (y, 0) = y) {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    (c : ℂ → Fin b → ℂ) {r E0 B0 B : ℝ} (hr : 0 < r) (hE0 : 0 ≤ E0)
    (hB0 : 0 ≤ B0) (hB : 0 ≤ B) (hE : (variationEnergy d j F).toReal ≤ E0)
    (hfamily : HolomorphicDiscFamily F (wallSprayFamily d j a Ψ F c) r)
    (hboundary : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ θ,
      wallSprayFamily d j a Ψ F c z (circlePoint θ) ∈ boundaryRegion d j)
    (hincrement : ∀ z ∈ Metric.ball (0 : ℂ) r,
      boundaryDSq (fun θ (_ : Unit) => (nativeLogIncrement d j a Ψ (F.f (circlePoint θ))
        (z, (outerWallPhase d j a F.f θ, c (circlePoint θ))) : ℂ)) ≤ ENNReal.ofReal (B0 ^ 2))
    (hjets : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ m : ℕ, 1 ≤ m → m ≤ 3 → ∀ v : Fin m → ℂ,
      boundaryDSq (fun θ (_ : Unit) =>
        (nativeIncrementJet d j a Ψ m (F.f (circlePoint θ))
          (z, (outerWallPhase d j a F.f θ, c (circlePoint θ)))).2 v) ≤
          ENNReal.ofReal ((B * ∏ i, ‖v i‖) ^ 2)) :
    ContDiffOn ℝ 3 (fun z => (scalarDSq (logTrace d j (wallSprayFamily d j a Ψ F c z))).toReal)
      (Metric.ball (0 : ℂ) r) ∧
    ∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖iteratedFDeriv ℝ 3 (fun p => (scalarDSq (logTrace d j (wallSprayFamily d j a Ψ F c p))).toReal) z‖ ≤
        2 * (Real.sqrt E0 + B0) * B + 6 * B ^ 2 := by
  let f : ℂ × ℝ → ℂ := fun p => (logTrace d j (wallSprayFamily d j a Ψ F c p.1) p.2 : ℂ)
  have hf : ContDiffOn ℝ ∞ f (Metric.ball (0 : ℂ) r ×ˢ Set.univ) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (family_logTrace_contDiffOn_of_boundary hd j hfamily hboundary)
  have hp : ∀ z ∈ Metric.ball (0 : ℂ) r, Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi) :=
    fun z _ θ => congrArg Complex.ofReal (logTrace_periodic d j {F with f := wallSprayFamily d j a Ψ F c z} θ)
  have henergy : variationEnergy d j F ≤ ENNReal.ofReal E0 :=
    (ENNReal.le_ofReal_iff_toReal_le hF.2.2.2.2.2.2.2.2 hE0).mpr hE
  have h0f : wallSprayFamily d j a Ψ F c 0 = F.f := wallSprayFamily_zero d j a hzero F c
  have hinit : boundaryDSq (fun θ (_ : Unit) => f (0, θ)) ≤ ENNReal.ofReal E0 := by
    change scalarDSq (logTrace d j (wallSprayFamily d j a Ψ F c 0)) ≤ _
    rw [h0f]
    exact (logTrace_scalarDSq_le_variationEnergy d j F).trans henergy
  have hdiff : ∀ z ∈ Metric.ball (0 : ℂ) r,
      boundaryDSq (fun θ (_ : Unit) => f (z, θ) - f (0, θ)) ≤ ENNReal.ofReal (B0 ^ 2) := by
    intro z hz
    convert hincrement z hz using 2
    funext θ k
    dsimp [f]
    rw [h0f, logTrace_wallSprayFamily_eq hd j a hF c z θ]
    push_cast
    ring
  have hjet : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ m : ℕ, 1 ≤ m → m ≤ 3 → ∀ v : Fin m → ℂ,
      boundaryDSq (fun θ (_ : Unit) => iteratedFDeriv ℝ m (fun p => f (p, θ)) z v) ≤
        ENNReal.ofReal ((B * ∏ i, ‖v i‖) ^ 2) := by
    intro z hz m hm hm3 v
    convert hjets z hz m hm hm3 v using 2
    funext θ k
    have heq : (fun p => f (p, θ)) = fun p => (logTrace d j F.f θ : ℂ) +
        (nativeLogIncrement d j a Ψ (F.f (circlePoint θ))
          (p, (outerWallPhase d j a F.f θ, c (circlePoint θ))) : ℂ) := by
      funext p
      dsimp [f]
      rw [logTrace_wallSprayFamily_eq hd j a hF c p θ, Complex.ofReal_add]
    rw [heq, iteratedFDeriv_const_shift _ _ m (by omega)]
    rfl
  exact ⟨(actual_traceEnergy_contDiffOn isOpen_ball hf hp).of_le (by simp),
    uniform_actual_traceEnergy_third_le isOpen_ball (Metric.mem_ball_self hr) hf hp
      hE0 hB0 hB hinit hdiff hjet⟩

end Yau.Blueprint.V02WallTaylorProof
