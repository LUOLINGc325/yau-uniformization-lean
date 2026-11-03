import Yau.Proofs.F01ChartGramSmooth

/-! The actual positive pullback determinant has a smooth real logarithm
throughout a holomorphic chart, with the original determinant convention. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem pullback_logdet_contDiffOn (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target) :
    ContDiffOn ℝ ∞ (fun z => Real.log (pullbackMatrix g e z).det.re) e.source := by
  have hd := Yau.LeafProofs.L12Aux.contDiffOn_matrix_det
    (fun i j => pullbackMatrix_entry_contDiffOn g hg e he i j)
  have hr := Complex.reCLM.contDiff.comp_contDiffOn hd
  exact hr.log (fun z hz => (pullbackMatrix_det_re_pos g e he hei hz).ne')

end Yau.NodeProofs.F01Aux
