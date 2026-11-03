import Yau.LeafProofs.L23DistanceEnergyFrames

/-! Genuine physical orthonormal frames compute exactly the original Ricci trace. -/

noncomputable section
open scoped Topology ContDiff Manifold Matrix
namespace Yau.LeafProofs.L23Aux
open L12Aux L18Aux L19Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {n : ℕ} {M : ComplexManifold n}

theorem curvaturePairBilin_metric_trace (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z∈chartTarget c) (T : ComplexVector n) :
    (∑ i, ∑ j, (realMetricFn h c z)⁻¹ i j*
      curvaturePairBilin h c z T (realVec i) (realVec j))=
        -(∑ i, ∑ j, realRicciCoeff h c z i j*realCoord T i*realCoord T j) := by
  obtain ⟨D,hD⟩ := inverseMetric_exists_gram_factor (realMetricFn h c z) (realMetricFn_posDef h c z hz)
  let W : RIdx n → ComplexVector n := fun s => ∑ i, D i s • realVec i
  have hW : ∀ i j, ∑ s, realCoord (W s) i*realCoord (W s) j=(realMetricFn h c z)⁻¹ i j := by
    intro i j
    simp only [W,realCoord_sum_realVec]
    rw [hD]
    rfl
  have hB := bilinear_frame_trace (curvaturePairBilin h c z T) (realMetricFn h c z)⁻¹ W hW
  have hR := connectionCurvature_frame_trace h hh c hz T W hW
  exact hB.symm.trans hR

theorem connectionCurvature_orthonormal_trace {κ : Type*} [Fintype κ] [DecidableEq κ]
    (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier) (T : ComplexVector n)
    (b : letI := underlyingRealTangentNormedAddCommGroup h x
      letI := underlyingRealTangentInnerProductSpace h x
      OrthonormalBasis κ ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x)) :
    (∑ s, realMetricInChart h x (chartPt x x)
      (connectionCurvature (chartChristoffelBilin h x) (chartPt x x)
        (realTangentCoords x x (b s)) T (realTangentCoords x x (b s))) T)=
      -(∑ i, ∑ j, realRicciCoeff h x (chartPt x x) i j*realCoord T i*realCoord T j) := by
  change (∑ s, curvaturePairBilin h x (chartPt x x) T
    (realTangentCoords x x (b s)) (realTangentCoords x x (b s)))=_
  rw [←chartBilinear_inverseMetric_trace_eq_orthonormal h x _ b]
  have hsym : ((realMetricFn h x (chartPt x x))⁻¹).IsSymm :=
    (L18Aux.realMetricFn_isSymm h x (chartPt x x)).inv
  have hpoint : chartPt x x∈chartTarget x := mem_extChartAt_target x
  calc
    _=∑ i, ∑ j, (realMetricFn h x (chartPt x x))⁻¹ i j*
        curvaturePairBilin h x (chartPt x x) T (realVec i) (realVec j) := by
      simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,realBilinMatrix_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsym.apply j i]
    _=_ := curvaturePairBilin_metric_trace h hh x hpoint T

end Yau.LeafProofs.L23Aux
