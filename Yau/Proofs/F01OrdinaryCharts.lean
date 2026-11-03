import Yau.Proofs.F01BufferedAtlas
import Yau.Proofs.F01RestrictedGram

/-! Ordinary inverse atlas charts are actual holomorphic parametrizations.
Their native Gram coefficients equal the fixed-chart hMat on the real target. -/
open Set
open scoped Manifold ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

def ordinaryChart (p : M.Carrier) : OpenPartialHomeomorph (ComplexVector n) M.Carrier :=
  (chartAt (ComplexVector n) p).symm

theorem ordinaryChart_apply (p : M.Carrier) (z : ComplexVector n) :
    ordinaryChart p z = chartInv p z := by
  unfold ordinaryChart chartInv extChartAt
  rw [complex_extend_eq]
  rfl

theorem ordinaryChart_source (p : M.Carrier) : (ordinaryChart p).source = chartTarget p := by
  unfold ordinaryChart chartTarget extChartAt
  rw [complex_extend_eq]
  rfl

theorem ordinaryChart_contMDiffOn (p : M.Carrier) :
    ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ (ordinaryChart p) (ordinaryChart p).source :=
  contMDiffOn_chart_symm (I := ComplexModel n) (n := ∞) (x := p)

theorem ordinaryChart_inverse_contMDiffOn (p : M.Carrier) :
    ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ (ordinaryChart p).symm (ordinaryChart p).target :=
  contMDiffOn_chart (I := ComplexModel n) (n := ∞) (x := p)

theorem ordinaryChart_chartVec (p : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget p)
    (v : ComplexVector n) :
    mfderiv (ComplexModel n) (ComplexModel n) (ordinaryChart p) z v =
      chartVec p (chartInv p z) v := by
  have heq : (ordinaryChart p : ComplexVector n → M.Carrier) = chartInv p :=
    funext (ordinaryChart_apply p)
  have hpt : chartPt p (chartInv p z) = z := (extChartAt (ComplexModel n) p).right_inv hz
  have hd := congrArg (fun f : ComplexVector n → M.Carrier =>
    mfderiv (ComplexModel n) (ComplexModel n) f z v) heq
  unfold chartVec
  rw [hpt]
  exact hd

theorem ordinaryChart_Gram (g : HermitianField M) (p : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget p) (i j : Fin n) :
    chartGramCoefficient g (ordinaryChart p) z i j = hMat g p z i j := by
  unfold chartGramCoefficient hMat
  simp only [ordinaryChart_chartVec p hz]
  exact congrArg (fun x : M.Carrier => (g x).toFun
    (chartVec p (chartInv p z) (stdVec i)) (chartVec p (chartInv p z) (stdVec j)))
      (ordinaryChart_apply p z)

end Yau.NodeProofs.F01Aux
