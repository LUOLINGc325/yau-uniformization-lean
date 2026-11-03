import Yau.Proofs.C04BoundedGeometryChartsTensorProductBounds
import Yau.Proofs.C04BoundedGeometryChartsPhysicalJacobi

/-! Intrinsic curvature controls the genuine Jacobi operator, including its two speed factors. -/

noncomputable section
open scoped Topology Manifold ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

theorem realJacobiCurvature_pair_eq_tensor (g : SmoothMetric M) (x : M.Carrier)
    (T u w : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    (underlyingRealRiemannianMetric g.form).inner x u (realJacobiCurvatureOperator g x T w) =
      tensorEvaluation (rmJet g.form x 0 (chartPt x x))
        (fun j => realCoord (realTangentCoords x x ((![w, T, T, u] : Fin 4 → _) j))) := by
  rw [← realMetricInChart_tangentCoords g.form x x (mem_chart_source _ _),
    realJacobiCurvatureOperator_apply, realTangentCoords_realFrameCLM x x (mem_chart_source _ _),
    realMetricInChart_symm]
  change realMetricInChart g.form x (chartPt x x)
      (connectionCurvature (chartChristoffelBilin g.form x) (chartPt x x)
        (realTangentCoords x x w) (realTangentCoords x x T) (realTangentCoords x x T))
      (realTangentCoords x x u) = _
  rw [Yau.NodeProofs.P02Aux.connectionCurvature_pair_eq_coordinateRm g.form
    (metricSmooth_of_smoothMetric g) x (z := chartPt x x) (mem_extChartAt_target x),
    Yau.NodeProofs.P02Aux.coordinateRm_eq_tensorEval, tensorEvalCLM_apply]
  rfl

theorem realJacobiCurvature_pair_abs_le (g : SmoothMetric M) (x : M.Carrier)
    (T u w : TangentSpace 𝓘(ℝ, ComplexVector n) x) {K S : ℝ}
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hcurv : curvatureJetNorm g.form 0 x ≤ K)
    (hT : (underlyingRealRiemannianMetric g.form).inner x T T ≤ S ^ 2)
    (hu : (underlyingRealRiemannianMetric g.form).inner x u u ≤ 1)
    (hw : (underlyingRealRiemannianMetric g.form).inner x w w ≤ 1) :
    |(underlyingRealRiemannianMetric g.form).inner x u (realJacobiCurvatureOperator g x T w)| ≤
      K * S ^ 2 := by
  rw [realJacobiCurvature_pair_eq_tensor]
  have H := curvature_jet_evaluation_le_product g.form x 0
    (![w, T, T, u]) (![1, S, S, 1]) hK (by
      intro j
      fin_cases j <;> simp [hS]) hcurv (by
      intro j
      fin_cases j
      · simpa using hw
      · exact hT
      · exact hT
      · simpa using hu)
  simpa [Fin.prod_univ_succ, pow_two, mul_assoc] using H

theorem realGeodesicCurvatureMatrix_entry_abs_le (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : curvatureJetNorm g.form 0 (realGeodesicFlow g q t).proj ≤ K)
    (i j : Fin (2 * n)) :
    |realGeodesicCurvatureMatrix g q t i j| ≤
      K * (underlyingRealRiemannianMetric g.form).inner q.proj q.2 q.2 := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let x := (realGeodesicFlow g q t).proj
  let e := realGlobalParallelFrame g q t
  have hspeed : (underlyingRealRiemannianMetric g.form).inner x
      (realGeodesicFlow g q t).2 (realGeodesicFlow g q t).2 = ‖q.2‖ ^ 2 := by
    have H := realGeodesicFlow_energy g q t
    rw [realTangentEnergy_eq_norm_sq, realTangentEnergy_eq_norm_sq] at H
    change ⟪(realGeodesicFlow g q t).2, (realGeodesicFlow g q t).2⟫_ℝ = _
    rw [real_inner_self_eq_norm_sq]
    exact H
  have hunit (a : Fin (2 * n)) : (underlyingRealRiemannianMetric g.form).inner x (e a) (e a) ≤ 1 := by
    change ⟪e a, e a⟫_ℝ ≤ 1
    simp only [real_inner_self_eq_norm_sq, e.norm_eq_one, one_pow, le_refl]
  have H := realJacobiCurvature_pair_abs_le g x (realGeodesicFlow g q t).2 (e i) (e j)
    hK (norm_nonneg q.2) hcurv hspeed.le (hunit i) (hunit j)
  change |realGeodesicCurvatureMatrix g q t i j| ≤ _ at H
  convert H using 1
  change K * ⟪q.2, q.2⟫_ℝ = _
  rw [real_inner_self_eq_norm_sq]

theorem physicalCurvatureOperator_norm_le (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : curvatureJetNorm g.form 0 (realGeodesicFlow g q t).proj ≤ K) :
    ‖physicalCurvatureOperator g q t‖ ≤
      ‖physicalMatrixMap n‖ *
        (K * (underlyingRealRiemannianMetric g.form).inner q.proj q.2 q.2) := by
  let β := K * (underlyingRealRiemannianMetric g.form).inner q.proj q.2 q.2
  have hβ : 0 ≤ β := by
    letI := underlyingRealTangentNormedAddCommGroup g.form q.proj
    letI := underlyingRealTangentInnerProductSpace g.form q.proj
    change 0 ≤ K * ⟪q.2, q.2⟫_ℝ
    exact mul_nonneg hK (real_inner_self_nonneg)
  have hm : ‖realGeodesicCurvatureMatrix g q t‖ ≤ β := by
    apply (pi_norm_le_iff_of_nonneg hβ).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hβ).mpr
    intro j
    exact realGeodesicCurvatureMatrix_entry_abs_le g q t hK hcurv i j
  exact ((physicalMatrixMap n).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left hm (norm_nonneg (physicalMatrixMap n)))

end Yau.Proofs.C04ChartsAux
