import Yau.Proofs.F01MetricFamilyEntries

/-! Jointly smooth actual complex metric entries give the original real
metric-family smoothness, with the frozen factor-two convention. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem metricFamilySmooth_of_complex_entries
    (h : ℝ → HermitianField M) {I : Set ℝ}
    (hentries : ∀ a i j, ContDiffOn ℝ ∞
      (fun p : ComplexVector n × ℝ => hMat (h p.2) a p.1 i j) (chartTarget a ×ˢ I)) :
    MetricFamilySmooth h I := by
  intro a i j
  have hr := Complex.reCLM.contDiff.comp_contDiffOn (hentries a i.1 j.1)
  have hi := Complex.imCLM.contDiff.comp_contDiffOn (hentries a i.1 j.1)
  by_cases hij : i.2 = j.2
  · apply ((contDiffOn_const (c := (2 : ℝ))).mul hr).congr
    intro p _
    simp only [Yau.LeafProofs.L12Aux.realMetricFn_entries, if_pos hij]
    rfl
  · by_cases hi0 : i.2 = 0
    · apply ((contDiffOn_const (c := (2 : ℝ))).mul hi.neg).congr
      intro p _
      simp only [Yau.LeafProofs.L12Aux.realMetricFn_entries, if_neg hij, if_pos hi0]
      rfl
    · apply ((contDiffOn_const (c := (2 : ℝ))).mul hi).congr
      intro p _
      simp only [Yau.LeafProofs.L12Aux.realMetricFn_entries, if_neg hij, if_neg hi0]
      rfl

end Yau.NodeProofs.F01Aux
