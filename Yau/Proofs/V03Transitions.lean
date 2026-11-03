import Yau.Proofs.V03Charts

/-! The induced cotangent transition is the dual of the actual base-chart
derivative. The source hypotheses are retained in every formula. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem chartVec_transition (x x' y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source)
    (hy' : y ∈ (extChartAt (ComplexModel n) x').source) (v : ComplexVector n) :
    chartVec x y (tangentCoordChange (ComplexModel n) x' x y v) = chartVec x' y v := by
  rw [chartVec_eq_coordChange x y hy, chartVec_eq_coordChange x' y hy',
    tangentCoordChange_comp ⟨⟨hy', hy⟩, mem_extChartAt_source y⟩]

theorem covectorCoords_transition (x x' y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source)
    (hy' : y ∈ (extChartAt (ComplexModel n) x').source) (ξ : Covector n) (i : Fin n) :
    covectorCoords x' y ξ i =
      ∑ k, (tangentCoordChange (ComplexModel n) x' x y (stdVec i)) k *
        covectorCoords x y ξ k := by
  change ξ (chartVec x' y (stdVec i)) = _
  rw [← chartVec_transition x x' y hy hy', covector_apply_chartVec]

theorem cotangentChart_transition_fiber (x x' : M.Carrier) {z : CotangentCoord n}
    (hz : z ∈ cotangentTarget x)
    (hy' : chartInv x z.1 ∈ (extChartAt (ComplexModel n) x').source) (i : Fin n) :
    (cotangentChart x' (cotangentChartInv x z)).2 i =
      ∑ k, (tangentCoordChange (ComplexModel n) x' x (chartInv x z.1) (stdVec i)) k *
        z.2 k := by
  change covectorCoords x' (chartInv x z.1)
    (covectorOfCoords x (chartInv x z.1) z.2) i = _
  rw [covectorCoords_transition x x' (chartInv x z.1)
    ((extChartAt (ComplexModel n) x).map_target hz.1) hy',
    covectorCoords_ofCoords x (chartInv x z.1)
      ((extChartAt (ComplexModel n) x).map_target hz.1)]

theorem chartTransition_contDiffAt (x x' : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x)
    (hy' : chartInv x z ∈ (extChartAt (ComplexModel n) x').source) :
    ContDiffAt ℂ ∞ (fun w => chartPt x' (chartInv x w)) z := by
  have hi : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ (chartInv x) z :=
    (contMDiffOn_extChartAt_symm (I := ComplexModel n) x).contMDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)
  have ho : ContMDiffAt (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞
      (chartPt x') (chartInv x z) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hy')
  exact (ho.comp z hi).contDiffAt

theorem chartTransition_fderiv_eq_coordChange (x x' : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) :
    fderiv ℂ (fun w => chartPt x' (chartInv x w)) z =
      tangentCoordChange (ComplexModel n) x x' (chartInv x z) := by
  rw [tangentCoordChange_def, ModelWithCorners.range_eq_univ, fderivWithin_univ]
  change fderiv ℂ (fun w => chartPt x' (chartInv x w)) z =
    fderiv ℂ (fun w => chartPt x' (chartInv x w)) (chartPt x (chartInv x z))
  have hpt : chartPt x (chartInv x z) = z :=
    (extChartAt (ComplexModel n) x).right_inv hz
  rw [hpt]

end Yau.Blueprint.V03Proof
