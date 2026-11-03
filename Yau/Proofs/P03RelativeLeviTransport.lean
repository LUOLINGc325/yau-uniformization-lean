import Yau.Proofs.P03LeviChartTransport
import Yau.LeafProofs.L23MetricNaturality

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs Yau.LeafProofs.L22Aux Yau.LeafProofs.L12Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- A relative Levi lower bound transforms with the genuine metric under
the same actual chart Jacobian. -/
theorem inChart_relativeLevi_transport (g : HermitianField M) {ψ : M.Carrier → ℝ}
    (hψ : SmoothFn ψ) (a b : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hb : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) (t : ℝ)
    (hbound : ∀ w : ComplexVector n,
      t * realMetricInChart g b (chartPt b (chartInv a z)) w w ≤
        complexLeviQuadratic (inChart b ψ) (chartPt b (chartInv a z)) w)
    (v : ComplexVector n) :
    t * realMetricInChart g a z v v ≤ complexLeviQuadratic (inChart a ψ) z v := by
  let T : ComplexVector n → ComplexVector n := fun y => chartPt b (chartInv a y)
  have hT : ContDiffAt ℂ 2 T z := (L18Aux.chartTransition_contDiffAt a b hz hb).of_le (by simp)
  have hr : fderiv ℝ T z v = fderiv ℂ T z v :=
    congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L v)
      ((hT.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ)
  have hg := L23Aux.realMetricInChart_change g a b hz hb v v
  change realMetricInChart g a z v v =
    realMetricInChart g b (T z) (fderiv ℝ T z v) (fderiv ℝ T z v) at hg
  rw [hr] at hg
  rw [hg, inChart_complexLevi_transition hψ a b hz hb]
  exact hbound _

end Yau.NodeProofs.P03Aux
