import Yau.Proofs.P06ScalarUniquenessRicciTrace
import Yau.Proofs.P06ScalarUniquenessRicciSymmetry

/-! The actual computed Ricci matrix is the inverse metric Chern trace. -/
noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.NodeProofs.G01Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem chernF_trace_eq_contraction
    (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (k l : Fin n) :
    Matrix.trace (chernF h x z k l) =
      ∑ p, ∑ q, (hMat h x z)⁻¹ p q * chernInChart h x z p q k l := by
  have hdet := (L12Aux.hMat_posDef h x z hz).isUnit.map Matrix.detMonoidHom
  have he : chernF h x z k l = (hMat h x z)⁻¹ * (hMat h x z * chernF h x z k l) := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  rw [he]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  exact chernF_lower h hs x z hz p q k l

/-- The index order is the paper's actual Levi convention: the Ricci entry
`a,b` contracts `R_{b bar a k bar l}`. -/
theorem ricciInChart_eq_chern_contraction
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : Fin n) :
    (-leviC (logDet h x) z) a b =
      ∑ k, ∑ l, (hMat h x z)⁻¹ k l * chernInChart h x z b a k l := by
  rw [← chernF_trace_eq_ricciInChart h hs hk x z hz b a,
    chernF_trace_eq_contraction h hs x z hz]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [chernInChart_pair_exchange h hs hk x z hz k l b a]

theorem ricci_eq_chern_contraction
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) (a b : Fin n) :
    ricci h x a b =
      ∑ k, ∑ l, (gMat h x)⁻¹ k l * chernCurvature h x b a k l := by
  exact ricciInChart_eq_chern_contraction h hs hk x (chartPt x x) (mem_extChartAt_target x) a b

end Yau.NodeProofs.P06Aux
