import Yau.LeafProofs.L23DistanceEnergyPhysicalTrace
import Yau.Proofs.C01RealTangentRicciJets

/-! The exact physical orthonormal trace of the genuine weighted second-variation density. -/

noncomputable section
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem realFrameEquiv_symm_eq_coords (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    (realFrameEquiv x).symm v = realTangentCoords x x v := by
  apply (realFrameEquiv x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have H : realFrameEquiv x (realTangentCoords x x v) = v := by
    change (realFrameEquiv x).toContinuousLinearMap (realTangentCoords x x v) = v
    rw [realFrameEquiv_toContinuousLinearMap, realFrameCLM_realTangentCoords x x (mem_chart_source _ _)]
  exact H.symm

theorem weighted_connectionCurvature_scale
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (z V T : ComplexVector n) (a : ℝ) :
    connectionCurvature Γ z (a • V) T (a • V) = a ^ 2 • connectionCurvature Γ z V T V := by
  simp only [← connectionCurvatureMap_apply, map_smul, smul_apply, smul_smul, pow_two]

theorem weighted_secondDensity_physical_trace
    (k : HermitianField M) (hk : MetricSmooth k) (y x : M.Carrier)
    (P : ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) x)
    (hP : ∀ v w : ComplexVector n,
      (underlyingRealRiemannianMetric k).inner x (P v) (P w) =
        realMetricInChart k y (chartPt y y) v w)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) (a b : ℝ)
    (e : letI := underlyingRealTangentNormedAddCommGroup k y
      letI := underlyingRealTangentInnerProductSpace k y
      OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y))
    (D : Fin (2*n) → ℝ)
    (hD : ∀ i, let V := realTangentCoords x x (P (realTangentCoords y y (e i)))
      let T := realTangentCoords x x v
      D i = 2 * realMetricInChart k x (chartPt x x) (b • V) (b • V) +
        2 * realMetricInChart k x (chartPt x x) T
          (connectionCurvature (chartChristoffelBilin k x) (chartPt x x) (a • V) T (a • V))) :
    (∑ i, D i) = 2 * (2*n : ℕ) * b ^ 2 - 2 * a ^ 2 * actualRealRicciQuadratic k x v := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup k z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace k z
  let Q := fieldFrameTransportIsometry k y x P hP
  let e' := e.map Q
  let T := realTangentCoords x x v
  let V := fun i : Fin (2*n) => realTangentCoords x x (e' i)
  have he' (i : Fin (2*n)) : e' i = P (realTangentCoords y y (e i)) := by
    change P ((realFrameEquiv y).symm (e i)) = P (realTangentCoords y y (e i))
    rw [realFrameEquiv_symm_eq_coords]
  have hNorm (i : Fin (2*n)) : realMetricInChart k x (chartPt x x) (V i) (V i) = 1 := by
    rw [realMetricInChart_tangentCoords k x x (mem_chart_source _ _)]
    exact e'.inner_eq_one i
  have hTrace : (∑ i, realMetricInChart k x (chartPt x x) T
      (connectionCurvature (chartChristoffelBilin k x) (chartPt x x) (V i) T (V i))) =
        -actualRealRicciQuadratic k x v := by
    have H := connectionCurvature_orthonormal_trace k hk x T e'
    simp only [realMetricInChart_symm k x (chartPt x x) T]
    rw [H]
    congr 1
    simp only [T, realRicciCoeff_eq_realRicciMatrix k x (chartPt x x) (mem_extChartAt_target x),
      realTangentCoords_eq_complex_self]
    rfl
  have hFormula (i : Fin (2*n)) : D i =
      2 * b ^ 2 * realMetricInChart k x (chartPt x x) (V i) (V i) +
      2 * a ^ 2 * realMetricInChart k x (chartPt x x) T
        (connectionCurvature (chartChristoffelBilin k x) (chartPt x x) (V i) T (V i)) := by
    rw [hD i]
    simp only [V, he', T, weighted_connectionCurvature_scale, map_smul, smul_apply, smul_eq_mul]
    ring
  simp only [hFormula, hNorm, mul_one, Finset.sum_add_distrib, ← Finset.mul_sum, hTrace,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Yau.NodeProofs.C01Aux
