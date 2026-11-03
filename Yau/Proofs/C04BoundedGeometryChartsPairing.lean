import Yau.Proofs.C04BoundedGeometryChartsExponential

/-! Exact metric normalization and the image-radius bound of the real exponential. -/

noncomputable section
open scoped Topology Manifold ContDiff Matrix InnerProductSpace

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem sum_stdVec (v : ComplexVector n) : ∑ i, v i • stdVec i = v := by
  ext j
  simp [stdVec, EuclideanSpace.single, Pi.single_apply]

theorem unitary_frame_pairing (k : HermitianField M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (k p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) (v w : ComplexVector n) :
    (k p).toFun (U v) (U w) = ⟪v, w⟫_ℂ := by
  have hsum (x : ComplexVector n) : U x = ∑ i, x i • U (stdVec i) := by
    calc
      U x = U (∑ i, x i • stdVec i) := congrArg U (sum_stdVec x).symm
      _ = _ := by simp only [map_sum, map_smul]
  rw [hsum v, hsum w, hermitian_sum_left]
  simp_rw [hermitian_sum_right, HermitianInnerProduct.map_smul_left,
    HermitianInnerProduct.map_smul_right, hU]
  simp [Matrix.one_apply, PiLp.inner_apply, mul_comm]

theorem realUnitaryFrame_norm (k : HermitianField M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (k p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) (v : ComplexVector n) :
    letI := underlyingRealTangentNormedAddCommGroup k p
    ‖realUnitaryFrame p U v‖ = Real.sqrt 2 * ‖v‖ := by
  letI := underlyingRealTangentNormedAddCommGroup k p
  rw [underlyingRealTangent_norm, realTangentEquiv_realUnitaryFrame]
  change Real.sqrt (2 * ((k p).toFun (U v) (U v)).re) = _
  rw [unitary_frame_pairing k p U hU]
  have hv : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  rw [hv]
  simp only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_sq (norm_nonneg _)]

theorem unitaryExponential_distance_le (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) (v : ComplexVector n) :
    inducedDistance g.form p (unitaryExponential g p U v) ≤ Real.sqrt 2 * ‖v‖ := by
  have H := inducedDistance_realExponentialMap_le g p (realUnitaryFrame p U v)
  rw [realUnitaryFrame_norm g.form p U hU] at H
  exact H

theorem unitaryExponential_mem_distBall (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) (v : ComplexVector n)
    {r : ℝ} (hr : 0 < r) (hv : Real.sqrt 2 * ‖v‖ < r) :
    unitaryExponential g p U v ∈ distBall g.form p r := by
  apply (Yau.LeafProofs.L12Aux.mem_distBall_iff g p _ hr).mpr
  exact (unitaryExponential_distance_le g p U hU v).trans_lt hv

end Yau.Proofs.C04ChartsAux
