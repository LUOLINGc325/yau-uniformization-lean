import Yau.Proofs.U02AnalyticSeries
import Mathlib.Geometry.Manifold.ContMDiff.Defs

open scoped ContDiff Topology Manifold
open Set Metric

namespace U02AnalyticAux

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℂ, F) ω N]

theorem contMDiffOn_omega_of_complex_infty
    {s : Set M} (hs : IsOpen s) {f : M → N}
    (hf : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f s) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, F) ω f s := by
  obtain ⟨hc, hcharts⟩ := (contMDiffOn_iff (n := ∞)).mp hf
  apply (contMDiffOn_iff (n := ω)).mpr
  refine ⟨hc, ?_⟩
  intro x y
  have hV : IsOpen (s ∩ f ⁻¹' (extChartAt 𝓘(ℂ, F) y).source) :=
    hc.isOpen_inter_preimage hs (isOpen_extChartAt_source y)
  have hW : IsOpen ((extChartAt 𝓘(ℂ, E) x).target ∩
      (extChartAt 𝓘(ℂ, E) x).symm ⁻¹'
        (s ∩ f ⁻¹' (extChartAt 𝓘(ℂ, F) y).source)) :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage
      (isOpen_extChartAt_target x) hV
  exact AnalyticOnNhd.contDiffOn_of_completeSpace
    (analyticOnNhd_of_complex_contDiffOn_infty hW (hcharts x y))

theorem contMDiff_omega_of_complex_infty {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f := by
  rw [← contMDiffOn_univ] at hf ⊢
  exact contMDiffOn_omega_of_complex_infty isOpen_univ hf

end U02AnalyticAux
