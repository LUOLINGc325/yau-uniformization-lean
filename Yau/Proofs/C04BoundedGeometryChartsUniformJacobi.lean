import Yau.Proofs.C04BoundedGeometryChartsCurvatureOperatorBound
import Yau.Proofs.C04BoundedGeometryChartsRadiusChoice

/-! A uniform radius for the genuine radial Jacobi differential. -/

noncomputable section
open Set
open scoped Topology Manifold ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

theorem unitaryExponential_radial_flow (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) (t : ℝ) :
    (realGeodesicFlow g (radialInitialState p U v) t).proj =
      unitaryExponential g p U (t • v) := by
  simp only [unitaryExponential, map_smul, realExponentialMap_smul]
  rfl

theorem unitary_initial_energy (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) (v : ComplexVector n) :
    (underlyingRealRiemannianMetric g.form).inner p
      (realUnitaryFrame p U v) (realUnitaryFrame p U v) = 2 * ‖v‖ ^ 2 := by
  rw [realUnitaryFrame_pairing, unitary_frame_pairing g.form p U hU]
  have H : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  rw [H]

theorem exists_uniform_physicalJacobi_radius (n : ℕ) (hn : 0 < n)
    (r K : ℝ) (hr : 0 < r) (hK : 0 < K) :
    ∃ s : ℝ, 0 < s ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M) (p : M.Carrier)
      (U : ComplexVector n ≃L[ℂ] TangentVector M p),
      (∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
        (1 : Matrix (Fin n) (Fin n) ℂ) i j) →
      (∀ x ∈ distBall g.form p (2 * r), curvatureJetNorm g.form 0 x ≤ K) →
      ∀ v ∈ Metric.ball (0 : ComplexVector n) (4 * s),
        unitaryExponential g p U v ∈ distBall g.form p (2 * r) ∧
        ‖physicalJacobiOperator g (radialInitialState p U v) 1 - 1‖ ≤ (1 / 4 : ℝ) := by
  let D := ‖physicalMatrixMap n‖
  obtain ⟨s, hs, hsr, hsmall⟩ := exists_uniform_normal_radius hr hK (norm_nonneg (physicalMatrixMap n))
  refine ⟨s, hs, ?_⟩
  intro M g p U hU hcurv v hv
  have hvnorm : ‖v‖ < 4 * s := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hballs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (realGeodesicFlow g (radialInitialState p U v) t).proj ∈ distBall g.form p (2 * r) := by
    rw [unitaryExponential_radial_flow]
    apply unitaryExponential_mem_distBall g p U hU (t • v) (by positivity)
    have hnorm : ‖t • v‖ ≤ ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    exact (mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg 2)).trans_lt
      ((mul_lt_mul_of_pos_left hvnorm (Real.sqrt_pos.mpr (by norm_num))).trans hsr)
  have himage : unitaryExponential g p U v ∈ distBall g.form p (2 * r) := by
    simpa only [unitaryExponential_radial_flow, one_smul] using hballs 1 (by norm_num)
  refine ⟨himage, ?_⟩
  have hR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖physicalCurvatureOperator g (radialInitialState p U v) t‖ ≤ (1 / 8 : ℝ) := by
    have H := physicalCurvatureOperator_norm_le g (radialInitialState p U v) t hK.le
      (hcurv _ (hballs t ht))
    change _ ≤ D * (K * (underlyingRealRiemannianMetric g.form).inner p
      (realUnitaryFrame p U v) (realUnitaryFrame p U v)) at H
    rw [unitary_initial_energy g p U hU] at H
    have hsquare : ‖v‖ ^ 2 ≤ (4 * s) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hvnorm.le
    apply H.trans
    calc
      D * (K * (2 * ‖v‖ ^ 2)) ≤ D * K * (2 * (4 * s) ^ 2) := by
        nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (physicalMatrixMap n)) hK.le)
          (sub_nonneg.mpr hsquare)]
      _ ≤ 1 / 8 := hsmall
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  exact jacobi_volterra_close_at_one _ _
    (continuous_iff_continuousAt.mpr
      (fun t => (physicalJacobiOperator_hasDerivAt g (radialInitialState p U v) t).continuousAt)).continuousOn
    (by norm_num) (by norm_num) hR (physicalJacobiOperator_volterra g _ hR)

end Yau.Proofs.C04ChartsAux
