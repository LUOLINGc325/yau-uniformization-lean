import Yau.Proofs.F01NativeNormalizedTerminalPasteSmooth
import Yau.Proofs.F01ActualTerminalIntervalSmooth
import Yau.Proofs.F01NativeCompatibleTerminalData
import Yau.Proofs.F01ActualTerminalRestart

/-! Genuine terminal construction, actual short-time existence and
the proved closed-face jet calculus give a smooth native restart.
Neither terminal realizations nor mixed jets are inputs. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_actual_smooth_terminal_restart
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
    ∃ (ε D : ℝ) (K : HermitianField M) (u : M.Carrier → ℝ)
      (hR : ℝ → HermitianField M) (W : M.Carrier → ℝ → ℝ),
      0 < ε ∧ 1 ≤ D ∧ MetricSmooth K ∧ SmoothFn u ∧ hR 0 = K ∧
      MetricFamilySmooth hR (Icc 0 ε) ∧ SmoothSpaceTime W (Icc 0 ε) ∧
      (∀ x, W x 0 = u x) ∧
      (∀ x, gMat K x = gMat g x - (Tstar : ℂ) • ricci g x + levi u x) ∧
      (∀ x s, s ∈ Icc 0 ε →
        (gMat (hR s) x - ((D⁻¹ : ℝ) : ℂ) • gMat K x).PosSemidef ∧
        ((D : ℂ) • gMat K x - gMat (hR s) x).PosSemidef ∧
        gMat (hR s) x = gMat g x - ((Tstar + s : ℝ) : ℂ) • ricci g x + levi (fun y => W y s) x ∧
        HasDerivWithinAt (W x) (flowLogDetRatio g hR x s) (Icc 0 ε) s) ∧
      SmoothSpaceTime (nativePastedRestartPotential U u W Tstar)
        (Ioo (Tstar - (ρ * (1 / 4)) ^ 2 / 4) (Tstar + ε)) := by
  let σ : ℝ := ρ * (1 / 4)
  have hσ : 0 < σ := mul_pos hρ (by norm_num)
  have hσr : σ ≤ A.radius := (by dsimp only [σ]; linarith : σ ≤ ρ).trans hρr
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
  have hEarly' : 0 ≤ Tstar - σ ^ 2 / 4 := (sq_nonneg ρ).trans hEarly
  obtain ⟨τ, hMono, hτ, hLim, K, u, hK, hu, hBG, hComplete, hOrders,
      hIdentity, hNative, hValues, hJets⟩ :=
    native_compatible_terminal_data g hg A hρ hρr hρ1 hTstar hC hEarly h U hU hU0 hpot hpde hflow
  obtain ⟨ε, D, hε, hD, hR, W, hR0, hhR, hW, hW0, hData⟩ :=
    exists_actual_lifted_terminal_restart g K hg hK hComplete hBG u hu Tstar hIdentity
  obtain ⟨B, hB, hHolder⟩ := partial_native_potential_jet_holder g hg A hρ hρr hρ1 hTstar hC
    (α := 1 / 2) (β := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hEarly
  have hr : 0 < ε / σ ^ 2 := div_pos hε hσ2
  have hrε : σ ^ 2 * (ε / σ ^ 2) ≤ ε := by
    rw [mul_div_cancel₀ ε hσ2.ne']
  have hProfiles := native_normalized_terminal_paste_smooth hg A h U K u hu hR W hσ hσr
    hEarly' hr hrε (show 0 < min (1 / 2 : ℝ) (1 / 4) by norm_num)
    hU hpot hpde hIdentity hW hW0
    (fun s hs x => (hData x s hs).2.2.1)
    (fun x s hs => (hData x s hs).2.2.2)
    B (hHolder h U hU hU0 hpot hpde hflow) τ hτ hLim hJets
  have hSmooth := smoothSpaceTime_on_actual_terminal_interval_of_normalized_profiles g hg A
    (nativePastedRestartPotential U u W Tstar) hσ hσr Tstar (ε / σ ^ 2) hProfiles
  have hClock : σ ^ 2 * (ε / σ ^ 2) = ε := mul_div_cancel₀ ε hσ2.ne'
  rw [hClock] at hSmooth
  exact ⟨ε, D, K, u, hR, W, hε, hD, hK, hu, hR0, hhR, hW, hW0,
    hIdentity, hData, hSmooth⟩

end Yau.NodeProofs.F01Aux
