import Yau.Proofs.F01NativeTerminalBoundedGeometry
import Yau.Proofs.F01NativeTerminalPotential
import Yau.Proofs.F01NativeTerminalPotentialIdentity

/-! One clock sequence constructs compatible terminal metric and
potential data, with the original native identity and actual complete
bounded geometry. These data have no supplied terminal realizations. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Manifold Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem native_compatible_terminal_data
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
      ∃ (K : HermitianField M) (u : M.Carrier → ℝ),
        MetricSmooth K ∧ SmoothFn u ∧ Yau.LeafCandidates.HermitianBoundedGeometry K ∧
        IsCompleteDistance (inducedDistance K) ∧
        (∀ x, (gMat K x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
          ((C : ℂ) • gMat g x - gMat K x).PosSemidef) ∧
        (∀ x, gMat K x = gMat g x - (Tstar : ℂ) • ricci g x + levi u x) ∧
        (∀ x, Tendsto (fun m => gMat (h (τ m)) x) atTop (𝓝 (gMat K x))) ∧
        (∀ x, Tendsto (fun m => U x (τ m)) atTop (𝓝 (u x))) ∧
        ∀ a q, TendstoUniformlyOn
          (fun m x => iteratedFDeriv ℝ q
            (fun z => (((ρ * (1 / 4)) ^ 2)⁻¹) * U ((A.chart a) ((ρ * (1 / 4)) • z)) (τ m)) x)
          (iteratedFDeriv ℝ q
            (fun z => (((ρ * (1 / 4)) ^ 2)⁻¹) * u ((A.chart a) ((ρ * (1 / 4)) • z))))
          atTop (ball 0 (1 / 2)) := by
  obtain ⟨τ, hMono, hτ, hLim, K, hK, hBG, hComplete, hNative, hOrders⟩ :=
    native_terminal_restart_geometry g hg A hρ hρr hρ1 hTstar hC hEarly
      h U hU hU0 hpot hpde hflow
  obtain ⟨u, hu, hValues, hJets⟩ := native_terminal_smooth_potential g hg A
    hρ hρr hρ1 hTstar hC hEarly h U hU hU0 hpot hpde hflow τ hτ hLim
  have hMem (m : ℕ) : τ m ∈ Ico 0 Tstar :=
    ⟨(sq_nonneg ρ).trans (hEarly.trans (hτ m).1.le), (hτ m).2⟩
  have hPos (m : ℕ) : 0 < τ m :=
    (sq_pos_of_pos hρ).trans_le (hEarly.trans (hτ m).1.le)
  have hSlice (m : ℕ) : SmoothFn (fun x => U x (τ m)) :=
    smoothSpaceTime_slice (hU (τ m) (hPos m).le (hτ m).2) ⟨(hPos m).le, le_rfl⟩
  have hIdentity : ∀ x, gMat K x = gMat g x - (Tstar : ℂ) • ricci g x + levi u x := by
    apply native_terminal_potential_identity_of_chart_jets g K A (fun m => h (τ m))
      (fun m x => U x (τ m)) u hSlice hu (σ := ρ * (1 / 4))
      (mul_ne_zero hρ.ne' (by norm_num)) τ Tstar hLim hNative
      (fun a => (hJets a 2).tendsto_at (mem_ball_self (by norm_num)))
      (fun m x => hpot (τ m) (hMem m) x)
  exact ⟨τ, hMono, hτ, hLim, K, u, hK, hu, hBG, hComplete, hOrders,
    hIdentity, hNative, hValues, hJets⟩

end Yau.NodeProofs.F01Aux
