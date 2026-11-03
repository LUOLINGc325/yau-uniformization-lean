import Yau.Proofs.F01ActualSmoothTerminalRestart
import Yau.Proofs.F01NativeRestartWholeIntervalSmooth
import Yau.Proofs.F01NativeRestartClosedClock
import Yau.Proofs.F01NativeRestartCoarseSandwich

/-! A uniformly comparable genuine partial potential solution has an
actual solution on a strictly longer closed interval. All witnesses,
the joined clock equation, and its finite coarse constant are constructed. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_actual_longer_native_solution
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
    ∃ (Tnew Cnew : ℝ) (hNew : ℝ → HermitianField M) (V : M.Carrier → ℝ → ℝ),
      Tstar < Tnew ∧ 1 ≤ Cnew ∧ hNew 0 = h 0 ∧ (∀ x, V x 0 = 0) ∧
      (∀ s, s < Tstar → hNew s = h s ∧ ∀ x, V x s = U x s) ∧
      MetricFamilySmooth hNew (Icc 0 Tnew) ∧ SmoothSpaceTime V (Icc 0 Tnew) ∧
      ∀ x t, t ∈ Icc 0 Tnew →
        (gMat (hNew t) x - ((Cnew⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((Cnew : ℂ) • gMat g x - gMat (hNew t) x).PosSemidef ∧
        gMat (hNew t) x = gMat g x - (t : ℂ) • ricci g x + levi (fun y => V y t) x ∧
        HasDerivWithinAt (V x) (flowLogDetRatio g hNew x t) (Icc 0 Tnew) t := by
  have hTpos : 0 < Tstar := by
    nlinarith [sq_pos_of_pos hρ, sq_nonneg (ρ * (1 / 4 : ℝ))]
  obtain ⟨ε, D, K, u, hR, W, hε, hD, hK, hu, hR0, hhR, hW, hW0, hTerminal, hData, hJoin⟩ :=
    exists_actual_smooth_terminal_restart g hg A hρ hρr hρ1 hTstar hC hEarly h U hU hU0 hpot hpde hflow
  have hδ : 0 < (ρ * (1 / 4)) ^ 2 / 4 := by positivity
  have hV := native_restart_paste_smooth_extended_interval U u W hδ hε hU hJoin
  have hRpot := fun s hs x => (hData x s hs).2.2.1
  have hRPde := fun x s hs => (hData x s hs).2.2.2
  have hMetric := native_restart_paste_metricFamilySmooth g hg h hR U u W hTstar hε hW0 hpot hRpot hV
  have hCoarse := native_restart_paste_coarse_sandwich g K h hR hTpos hε hC hD hR0 hMetric hflow
    (fun x s hs => ⟨(hData x s hs).1, (hData x s hs).2.1⟩)
  have hClock := native_restart_paste_closed_time_equation g h hR U u W hTpos hε hW0 hpde hRPde hV
  refine ⟨Tstar + ε / 2, C * D, nativePastedRestartFlow h hR Tstar,
    nativePastedRestartPotential U u W Tstar, by linarith, hCoarse.1, ?_, ?_, ?_, hMetric, hV, ?_⟩
  · exact if_pos hTpos
  · intro x
    exact (nativePastedRestartPotential_before U u W Tstar x hTpos).trans (hU0 x)
  · intro s hs
    exact ⟨if_pos hs, fun x => nativePastedRestartPotential_before U u W Tstar x hs⟩
  · intro x t ht
    have hOrder := hCoarse.2 x t ht
    exact ⟨hOrder.1, hOrder.2,
      nativePastedRestartFlow_potential_identity g h hR U u W Tstar ε hW0 hpot hRpot t
        ⟨ht.1, by linarith [ht.2]⟩ x,
      hClock x t ht⟩

end Yau.NodeProofs.F01Aux
