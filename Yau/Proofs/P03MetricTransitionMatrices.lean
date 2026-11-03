import Yau.Proofs.P03MetricDescent

open scoped Manifold Topology ContDiff Matrix
open Yau.LeafProofs

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem hMat_chart_change (g : HermitianField M) (a b x : M.Carrier)
    (ha : x ∈ (extChartAt (ComplexModel n) a).source)
    (hb : x ∈ (extChartAt (ComplexModel n) b).source) :
    hMat g a (chartPt a x) = (determinantTransitionMatrix a b x)ᴴ *
      hMat g b (chartPt b x) * determinantTransitionMatrix a b x := by
  rw [hMat_chartFrameGram g a x ha, hMat_chartFrameGram g b x hb,
    determinantTransitionMatrix_eq_basisMatrix a b x ha hb]
  exact hermitianGram_changeBasis (g x)
    (determinantFrameBasis b x hb) (determinantFrameBasis a x ha)

theorem determinantTransitionMatrix_mul_reverse (a b x : M.Carrier)
    (ha : x ∈ (extChartAt (ComplexModel n) a).source)
    (hb : x ∈ (extChartAt (ComplexModel n) b).source) :
    determinantTransitionMatrix a b x * determinantTransitionMatrix b a x = 1 := by
  rw [determinantTransitionMatrix_eq_basisMatrix a b x ha hb,
    determinantTransitionMatrix_eq_basisMatrix b a x hb ha]
  exact (determinantFrameBasis b x hb).toMatrix_mul_toMatrix_flip (determinantFrameBasis a x ha)

theorem determinantTransitionMatrix_entry_contMDiffOn (a b : M.Carrier) (i j : Fin n) :
    ContMDiffOn (ComplexModel n) 𝓘(ℂ, ℂ) ⊤
      (fun x => determinantTransitionMatrix a b x i j)
      ((extChartAt (ComplexModel n) a).source ∩ (extChartAt (ComplexModel n) b).source) := by
  have he : ContDiff ℂ ⊤ (fun L : ComplexVector n →L[ℂ] ComplexVector n => L (stdVec j) i) := by
    fun_prop
  exact (contMDiff_iff_contDiff.mpr he).comp_contMDiffOn (determinantTransition_contMDiffOn a b)

end Yau.NodeProofs.P03Aux
