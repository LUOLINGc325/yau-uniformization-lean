import Yau.Proofs.G01RealRmChern
import Yau.Proofs.G01BisectionalAlgebra
import Yau.Proofs.G01Homogeneity

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

/-- The numerator factor four holds at every point of every actual chart target. -/
theorem realRmInChart_bisectional_eq_four (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (U V : ComplexVector n) :
    realRmInChart h x z U V V U +
      realRmInChart h x z U (Complex.I • V) (Complex.I • V) U =
      4 * (∑ i, ∑ j, ∑ k, ∑ l,
        chernInChart h x z i j k l * U i * star (U j) * V k * star (V l)).re := by
  rw [realRmInChart_eq_chern h hs hk x z hz,
    realRmInChart_eq_chern h hs hk x z hz]
  change 2 * (mixedChernContraction (chernInChart h x z) U V V U).re +
    2 * (mixedChernContraction (chernInChart h x z) U
      (Complex.I • V) (Complex.I • V) U).re = _
  rw [mixed_bisectional_sum, holomorphic_symmetry_contraction _
    (chern_holomorphic_symm h hs hk x z hz) U V]

/-- The paper's two actual real sections sum to four times the computed Chern contraction. -/
theorem paper_numerator_eq_bisectionalForm (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (u v : TangentVector M x) :
    paperBisectionalNumerator h x u v =
      4 * bisectionalForm h x (tangentCoordinates x u) (tangentCoordinates x v) := by
  let U := tangentCoords x x u
  let V := tangentCoords x x v
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hJ : tangentCoords x x (Complex.I • v) = Complex.I • tangentCoords x x v :=
    (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) x) x).map_smul Complex.I v
  unfold paperBisectionalNumerator paperComplexStructure
  rw [paperRm_eq_realRmInChart, paperRm_eq_realRmInChart, hJ]
  rw [realRmInChart_eq_chern h hs hk x (chartPt x x) hz,
    realRmInChart_eq_chern h hs hk x (chartPt x x) hz]
  change 2 * (mixedChernContraction (chernInChart h x (chartPt x x)) U V V U).re +
    2 * (mixedChernContraction (chernInChart h x (chartPt x x)) U
      (Complex.I • V) (Complex.I • V) U).re = _
  rw [mixed_bisectional_sum, holomorphic_symmetry_contraction _
    (chern_holomorphic_symm h hs hk x (chartPt x x) hz) U V]
  simp only [chernInChart_center]
  rfl

/-- The factor-four bridge uses the original Basic calculator, including zero vectors. -/
theorem paperBisectionalNumerator_eq_four (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (u v : TangentVector M x) :
    paperBisectionalNumerator h x u v = 4 * (bisectionalNumeratorOnTangent h x u v).re := by
  rw [paper_numerator_eq_bisectionalForm h hs hk,
    bisectionalNumeratorOnTangent_re_eq h hs]

end Yau.NodeProofs.G01Aux
