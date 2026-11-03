import Yau.LeafProofs.L17InteriorCoordinates
import Yau.Proofs.F01OrdinaryCharts
import Yau.Proofs.F01MatrixSmooth

/-! Genuine ordinary-chart data from the original MetricSmooth field and
SmoothFn exhaustion. All tensor coefficients use the actual chart derivative. -/
open Set
open scoped Manifold ContDiff ComplexOrder Matrix.Norms.Frobenius
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem pullbackMatrix_entry_eq_chartGram (g : HermitianField M)
    (e : ComplexVector n → M.Carrier) (z : ComplexVector n) (i j : Fin n) :
    L17Aux.pullbackMatrix g e z i j = chartGramCoefficient g e z i j := rfl

theorem ordinary_coordinate_contDiffOn {u : M.Carrier → ℝ} (hu : SmoothFn u) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => u (ordinaryChart p z)) (chartTarget p) := by
  apply (hu p).congr
  intro z _
  exact congrArg u (ordinaryChart_apply p z)

theorem ordinary_gram_entry_contDiffOn {g : HermitianField M} (hg : MetricSmooth g)
    (p : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => L17Aux.pullbackMatrix g (ordinaryChart p) z i j) (chartTarget p) := by
  apply (L17Aux.hMat_contDiffOn_of_metricSmooth g hg p i j).congr
  intro z hz
  exact ordinaryChart_Gram g p hz i j

theorem ordinary_gram_contDiffOn {g : HermitianField M} (hg : MetricSmooth g) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => L17Aux.pullbackMatrix g (ordinaryChart p) z) (chartTarget p) :=
  matrix_contDiffOn_of_entries (ordinary_gram_entry_contDiffOn hg p)

theorem ordinary_gram_posDef (g : HermitianField M) (p : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget p) : (L17Aux.pullbackMatrix g (ordinaryChart p) z).PosDef := by
  apply L17Aux.pullbackMatrix_posDef g (ordinaryChart p)
    ((ordinaryChart_contMDiffOn p).mdifferentiableOn (by simp))
    ((ordinaryChart_inverse_contMDiffOn p).mdifferentiableOn (by simp))
  rwa [ordinaryChart_source]

end Yau.NodeProofs.F01Aux
