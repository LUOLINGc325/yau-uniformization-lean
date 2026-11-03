import Yau.Proofs.P06CylinderRegularityCompactInitial
import Yau.Proofs.P06ChartLocalL2

/-! The fixed near cutoff agrees with the original datum as a chart
germ on the physical compact used by the local norm estimate. -/
noncomputable section
open Filter
open scoped Topology

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.LeafProofs.L03

theorem physicalSupport_contains_chartInv {n : ℕ} {M : ComplexManifold n}
    (x : M.Carrier) (φ : ComplexVector n → ℝ) {K : Set (ComplexVector n)}
    (hOne : ∀ z ∈ K, φ z=1) :
    chartInv x '' K ⊆ CylinderChartL2.physicalSupport x φ := by
  apply Set.image_mono
  intro z hz
  apply subset_tsupport
  show φ z ≠ 0
  rw [hOne z hz]
  norm_num

theorem cutoff_component_germ_of_ball_plateau {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ)
    (A : RealForm M k) (J : ℕ) (R : ℝ)
    (hPlateau : ∀ y ∈ distBall g.form o R, CutoffTail.cutoffScalar χ J y=1)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (hBall : chartInv x z ∈ distBall g.form o R) (I : Fin k → RIdx n) :
    (fun w => formComponents (CutoffTail.cutoffForm χ A J) x w I) =ᶠ[𝓝 z]
      (fun w => formComponents A x w I) := by
  have hc : ContinuousAt (chartInv x) z := continuousAt_extChartAt_symm'' hz
  have he := hc.eventually ((Yau.LeafProofs.L12Aux.isOpen_distBall g o R).mem_nhds hBall)
  filter_upwards [he] with w hw
  simp only [CutoffTail.cutoffForm,formComponents_multiplyRealForm,inChart,hPlateau _ hw,one_mul]

end Yau.NodeProofs.P06Aux.CylinderReg
