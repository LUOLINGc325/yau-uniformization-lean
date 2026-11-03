import Yau.Proofs.V02FlowNativeCharts

/-! Smoothness of the actual spray in any valid fixed cotangent chart. -/

open scoped Manifold Topology ContDiff
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof V02FlowProof

variable {n b : ℕ} {M : ComplexManifold n}

theorem nativeSprayCoordinate_contDiffAt
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    {U : Set (NativeCotangentPoint M)} {R : ℝ} (hU : IsOpen U)
    (hΨ : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ ball 0 R))
    (x : M.Carrier) {u : CotangentCoord n} {τ : Fin b → ℂ}
    (hu : u ∈ cotangentTarget x)
    (hI : NativeCotangentPoint.mk (cotangentChartInv x u) ∈ U)
    (hτ : τ ∈ ball (0 : Fin b → ℂ) R)
    (hsource : (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u), τ)).val ∈
      cotangentSource x) :
    ContDiffAt ℂ ∞ (fun p : CotangentCoord n × (Fin b → ℂ) =>
      cotangentChart x (Ψ (NativeCotangentPoint.mk (cotangentChartInv x p.1), p.2)).val)
      (u, τ) := by
  have hInv := (nativeCotangentChartInv_contMDiffOn x).contMDiffAt
    ((nativeCotangentChartHomeomorph x).open_target.mem_nhds hu)
  have hfst : ContMDiffAt 𝓘(ℂ, CotangentCoord n × (Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞
      (Prod.fst : CotangentCoord n × (Fin b → ℂ) → CotangentCoord n) (u, τ) :=
    (contDiff_fst : ContDiff ℂ ∞
      (Prod.fst : CotangentCoord n × (Fin b → ℂ) → CotangentCoord n)).contMDiff.contMDiffAt
  have hsnd : ContMDiffAt 𝓘(ℂ, CotangentCoord n × (Fin b → ℂ))
      𝓘(ℂ, Fin b → ℂ) ∞
      (Prod.snd : CotangentCoord n × (Fin b → ℂ) → Fin b → ℂ) (u, τ) :=
    (contDiff_snd : ContDiff ℂ ∞
      (Prod.snd : CotangentCoord n × (Fin b → ℂ) → Fin b → ℂ)).contMDiff.contMDiffAt
  have hpair := (hInv.comp (u, τ) hfst).prodMk hsnd
  have hψ := (hΨ.contMDiffAt ((hU.prod isOpen_ball).mem_nhds ⟨hI, hτ⟩)).comp
    (u, τ) hpair
  have hchart := (nativeCotangentChart_contMDiffOn x).contMDiffAt
    ((nativeCotangentChartHomeomorph x).open_source.mem_nhds hsource)
  exact (hchart.comp (u, τ) hψ).contDiffAt

end Yau.Blueprint.V02Proof
