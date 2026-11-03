import Yau.Proofs.V02AreaTaylorCompact
import Yau.Proofs.V02AreaTaylorVelocity

/-! Each genuine finite chart piece has a uniform parameter derivative
majorant in the original immersion/Fourier first-disc velocity weight. -/

open scoped Topology ContDiff Matrix Manifold
open Filter

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof
open Yau Yau.Blueprint V03Proof

set_option synthInstance.maxHeartbeats 100000

variable {n q b : ℕ} {X : KahlerManifold n}

theorem chart_spatialDensity_uniform_jet_bound {d : VariationData X q}
    (hG : CotangentImmersion d.G)
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (x : Pt X) (a : CotangentCoord n) {δ R C0 : ℝ}
    (hδ : 0 < δ) (hR : 0 < R) (hC : 0 ≤ C0)
    (htarget : Metric.closedBall a δ ⊆ cotangentTarget x)
    (hψ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball a (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ u ∈ Metric.closedBall a δ,
      ∀ τ ∈ Metric.closedBall (0 : Fin b → ℂ) (R / 2),
        (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u), τ)).val ∈ cotangentSource x)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : ℂ → CotangentPoint X.manifold), CotangentDisc f →
      ∀ (h : ℂ → ℂ), ContDiffOn ℂ ∞ h (Metric.closedBall 0 1) →
      ∀ (c : ℂ → ComplexVector b), ContDiffOn ℂ ∞ c (Metric.closedBall 0 1) →
      (∀ z ∈ Metric.ball (0 : ℂ) (2 * sprayRadius R C0), CotangentDisc (sprayFamily Ψ f h c z)) →
      ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, f ζ ∈ cotangentSource x →
        cotangentChart x (f ζ) ∈ Metric.closedBall a δ → ‖h ζ‖ ≤ 1 → ‖c ζ‖ ≤ C0 →
      ∀ z ∈ Metric.closedBall (0 : ℂ) (sprayRadius R C0),
        ‖iteratedFDeriv ℝ k (fun p => spatialDensity d (sprayFamily Ψ f h c p) ζ) z‖ ≤
          C * inputDerivativeWeight (fun η => d.G (f η)) h c ζ := by
  obtain ⟨B, hB, hkernel⟩ := local_spray_kernel_uniform_jet_bound hG x a hδ hR hC hψ hsource k
  obtain ⟨L, hL, hchart⟩ := compact_immersion_chart_differential_bound hG x
    (isCompact_closedBall a δ) htarget
  refine ⟨B * (L + 1) ^ 2, mul_nonneg hB (sq_nonneg _), ?_⟩
  intro f hf h hh c hc hslice ζ hζ hx hu hh0 hc0 z hz
  have hr := sprayRadius_pos hR hC
  have hz2 : z ∈ Metric.ball (0 : ℂ) (2 * sprayRadius R C0) :=
    Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt (by linarith))
  have hformula : (fun p => spatialDensity d (sprayFamily Ψ f h c p) ζ) =ᶠ[𝓝 z]
      (fun p => complexDiagonal (localSpatialKernel d Ψ x (p, inputData x f h c ζ))
        (closedDiscDerivative (inputData x f h c) ζ)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz2] with p hp
    have htime := sprayTimes_mem_half hR hC
      (le_of_lt (by simpa using Metric.mem_ball.mp hp)) hh0 hc0
    have hdom : (p, inputData x f h c ζ) ∈ localSprayDomain a δ R := by
      refine ⟨?_, ?_⟩
      · exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hu).trans_lt (by linarith))
      · exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp htime).trans_lt (by linarith))
    have hy : sprayFamily Ψ f h c p ζ ∈ cotangentSource x := by
      simpa only [sprayFamily, cotangentChart_left_inv x hx] using
        hsource (cotangentChart x (f ζ)) hu _ htime
    exact spatialDensity_eq_localKernel hG hf hh hc x hψ hζ hx hdom (hslice p hp) hy
  rw [(hformula.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
  have hcompact : (z, inputData x f h c ζ) ∈ sprayCompactData a δ (sprayRadius R C0) C0 := by
    exact ⟨hz, hu, by simpa [inputData] using hh0, by simpa [inputData] using hc0⟩
  calc
    _ ≤ B * ‖closedDiscDerivative (inputData x f h c) ζ‖ ^ 2 := hkernel _ hcompact _
    _ ≤ B * ((L + 1) ^ 2 * inputDerivativeWeight (fun η => d.G (f η)) h c ζ) :=
      mul_le_mul_of_nonneg_left
        (norm_inputData_derivative_sq_le hG hf hh hc hζ x hx hL (hchart _ hu)) hB
    _ = _ := by ring

end Yau.Blueprint.V02AreaTaylorProof
