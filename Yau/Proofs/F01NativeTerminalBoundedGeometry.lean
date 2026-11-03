import Yau.Proofs.F01NativeTerminalMetric
import Yau.Proofs.F01TerminalRestartGeometry

/-! The genuine terminal slice retains all-order bounded geometry
and induced-distance completeness. These are consequences of native
subhorizon estimates and actual convergence, not continuation inputs. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Manifold Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem native_terminal_restart_geometry
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {ρ Tstar C : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρ1 : ρ ≤ 1)
    (hTstar : 0 ≤ Tstar) (hC : 1 ≤ C)
    (hEarly : ρ ^ 2 ≤ Tstar - (ρ * (1 / 4)) ^ 2 / 4)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (hU : ∀ T, 0 ≤ T → T < Tstar → SmoothSpaceTime U (Icc 0 T))
    (hU0 : ∀ x, U x 0 = 0)
    (hpot : ∀ s ∈ Ico 0 Tstar, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ T, 0 ≤ T → T < Tstar → ∀ x s, s ∈ Icc 0 T →
      HasDerivWithinAt (U x) (flowLogDetRatio g h x s) (Icc 0 T) s)
    (hflow : ∀ x s, s ∈ Ico 0 Tstar →
      (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) :
    ∃ τ : ℕ → ℝ, StrictMono τ ∧
      (∀ m, τ m ∈ Ioo (Tstar - (ρ * (1 / 4)) ^ 2 / 4) Tstar) ∧
      Tendsto τ atTop (𝓝 Tstar) ∧
      ∃ K : HermitianField M, MetricSmooth K ∧
        Yau.LeafCandidates.HermitianBoundedGeometry K ∧ IsCompleteDistance (inducedDistance K) ∧
        (∀ x, Tendsto (fun m => gMat (h (τ m)) x) atTop (𝓝 (gMat K x))) ∧
        (∀ x, (gMat K x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
          ((C : ℂ) • gMat g x - gMat K x).PosSemidef) := by
  let σ : ℝ := ρ * (1 / 4)
  have hσ : 0 < σ := mul_pos hρ (by norm_num)
  have hσr : σ ≤ A.radius := (show σ ≤ ρ by dsimp only [σ]; linarith [hρ.le]).trans hρr
  obtain ⟨τ, hMono, hτ, hLim, K, hSmooth, hNative, hOrders, hJets⟩ :=
    native_terminal_smooth_hermitian_field g hg A hρ hρr hρ1 hTstar hC hEarly
      h U hU hU0 hpot hpde hflow
  obtain ⟨B, _, hB⟩ := partial_native_matrix_jet_holder g hg A hρ hρr hρ1 hTstar hC
    (α := 1 / 4) (β := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hEarly
  have hBounds (a : M.Carrier) (q m : ℕ) (x : Space n) (hx : x ∈ ball 0 (1 / 2)) :
      ‖iteratedFDeriv ℝ q
        (fun z => pullbackMatrix (h (τ m)) (A.chart a) (σ • z)) x‖ ≤ B q :=
    (hB h U hU hU0 hpot hpde hflow a q).2.1 (x, τ m) ⟨hx, hτ m⟩
  have hGeometry := restart_geometry_of_actual_chart_jet_limits g K hg hSmooth A
    (fun m => h (τ m)) hσ hσr (show 0 < C by linarith) hOrders B hBounds hJets
  exact ⟨τ, hMono, hτ, hLim, K, hSmooth, hGeometry.1, hGeometry.2, hNative, hOrders⟩

end Yau.NodeProofs.F01Aux
