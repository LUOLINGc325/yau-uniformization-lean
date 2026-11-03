import Yau.LeafProofs.L17NonlinearBaseExistence

/-! Select the original nonlinear solution data and transport cutoff budget once. -/

noncomputable section
open Set Metric
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

namespace Yau.LeafProofs.L17BootstrapOriginalDataAux
open L17Aux L17HolderAux L17SchauderAux L17LocalizedSchauderAux

variable {n : ℕ} {M : ComplexManifold n}

/-- The original geometry supplies one global datum, before any local patch is chosen. -/
theorem exists_original_bootstrap_data (g : HermitianField M) (hg : MetricSmooth g)
    (hbg : LeafCandidates.HermitianBoundedGeometry g) :
    ∃ P : UniformChartPartition g, ∃ N : ℕ, ∃ Ccut : ℝ,
      0 ≤ Ccut ∧ P.overlapBudget ≤ N ∧ CutoffJetBounds P 2 Ccut ∧
      ∃ hr : P.radius ≤ 1, 2*P.radius < P.charts.radius ∧
        ∃ T : ℝ, ∃ hT : 0 < T, ∃ hTime : T ≤ P.radius^2,
          NonlinearBaseAt P T hT hTime hr := by
  obtain ⟨A⟩ := exists_boundedChartFamily g hbg
  obtain ⟨N,B,hB,hAll⟩ := A.exists_nonlinear_base hg
  obtain ⟨P,hPA,_hR,hN,hJets,hr,h2rho,T,hT,hTime,hBase⟩ := hAll 1 (by norm_num)
  let Ccut := ∑ j ∈ Finset.range 4, B j
  have hCcut : 0 ≤ Ccut := Finset.sum_nonneg (fun j _ => (hB j).le)
  have hRhoP : 2*P.radius < P.charts.radius := by simpa only [hPA] using h2rho
  have hCut : CutoffJetBounds P 2 Ccut := by
    apply cutoffJetBounds_of_all_orders P B (fun k => (hB k).le)
    intro k p q z hz
    exact scale_backgroundChart_jet_bound P.charts (P.localization_smooth p)
      P.radius_pos hRhoP q k (B k) (fun w hw => (hJets k p q w hw).2) hz
  exact ⟨P,N,Ccut,hCcut,hN.le,hCut,hr,hRhoP,T,hT,hTime,hBase⟩

end Yau.LeafProofs.L17BootstrapOriginalDataAux
