import Yau.LeafProofs.L17LocalizedSchauderUniformAssembly
import Yau.LeafProofs.L17UniformPartitionJets

open Set Metric
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- The accepted bounded-geometry partition constructor supplies all finite
cutoff hypotheses of the actual assembly. Every constant is fixed before
the requested radius, time cylinder, and local data. -/
theorem exists_uniform_partition_schauder_assembly (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (gamma : ℝ) (hγ : 0 < gamma) (hγone : gamma ≤ 1) :
    ∃ (N : ℕ) (B : ℕ → ℝ) (C : ℝ), (∀ k, 0 < B k) ∧ 0 < C ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ P : UniformChartPartition g,
        P.charts = A ∧ P.radius < epsilon ∧ P.radius ≤ 1 ∧ 2*P.radius < A.radius ∧ P.overlapBudget = N ∧
        (∀ k (p : P.centers) q z, z ∈ ball (0 : ComplexVector n) 2 →
          ‖iteratedFDeriv ℝ k (fun w => P.weight p (P.charts.chart q (P.radius • w))) z‖ ≤ B k ∧
          ‖iteratedFDeriv ℝ k (unitCutoff P p q) z‖ ≤ B k) ∧
        ∀ (T : ℝ) (hT : 0 < T) (F : ℝ), 0 ≤ F →
          ∀ (v : P.centers → ComplexVector n × Time T → ℝ)
            (D : P.centers → ComplexVector n × Time T → D1 n)
            (H : P.centers → ComplexVector n × Time T → D2 n)
            (b : P.centers → ComplexVector n × Time T → ℝ),
          LocalTrueJets P T hT.le v D H b → LocalScaledJetBounds P T gamma F v D H b →
            ∃! u : SchauderSpace P T gamma hT, schauderFun u = globalSum P T v ∧ ‖u‖ ≤ C*F := by
  obtain ⟨N,B,hB,hPartition⟩ := A.exists_uniform_partition_scaled_jet_budget hg
  let Ccut := ∑ j ∈ Finset.range 4, B j
  have hCcut : 0 ≤ Ccut := Finset.sum_nonneg (fun j _ => (hB j).le)
  obtain ⟨C,hC,hAssembly⟩ := exists_uniform_localized_schauder_assembly A hg N Ccut gamma hCcut hγ hγone
  refine ⟨N,B,C,hB,hC,?_⟩
  intro epsilon hepsilon
  obtain ⟨P,hPA,hRho,hOne,hSmall,hN,hJets⟩ := hPartition epsilon hepsilon
  have hCut : CutoffJetBounds P 2 Ccut := cutoffJetBounds_of_all_orders P B
    (fun k => (hB k).le) (fun k p q z hz => (hJets k p q z hz).2)
  exact ⟨P,hPA,hRho,hOne,hSmall,hN,hJets,
    hAssembly P hPA hN.le hOne hSmall hCut⟩

end Yau.LeafProofs.L17LocalizedSchauderAux
