import Yau.Proofs.C04BoundedGeometryChartsCoframeJacobi
import Yau.Proofs.C04BoundedGeometryChartsUniformJacobi
import Yau.Proofs.C04BoundedGeometryChartsRadialJ
import Yau.Proofs.C04BoundedGeometryChartsOperatorInverse

/-! Quantitative nonsingularity of the genuine exponential coframe on one uniform ball. -/

noncomputable section
open scoped Topology Manifold ContDiff Matrix

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

theorem radialCoframe_close_of_physicalJacobi (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) (v : ComplexVector n)
    (hJ : ‖physicalJacobiOperator g (radialInitialState p U v) 1 - 1‖ ≤ (1 / 4 : ℝ)) :
    ‖radialCoframe g p U v - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ) := by
  let B := initialPhysicalCoordinates g p U
  let Y := physicalJacobiOperator g (radialInitialState p U v) 1
  have hrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro w
  have H (z : ComplexVector n) : ‖B z‖ = Real.sqrt 2 * ‖z‖ :=
    initialPhysicalCoordinates_norm g p U hU z
  have heq : B ((radialCoframe g p U v - ContinuousLinearMap.id ℝ (ComplexVector n)) w) = (Y - 1) (B w) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub,
      radialCoframe_eq_physicalJacobi, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearMap.one_apply, B, Y]
  apply (mul_le_mul_iff_right₀ hrt).mp
  calc
    Real.sqrt 2 * ‖(radialCoframe g p U v - ContinuousLinearMap.id ℝ (ComplexVector n)) w‖ =
        ‖B ((radialCoframe g p U v - ContinuousLinearMap.id ℝ (ComplexVector n)) w)‖ := (H _).symm
    _ = ‖(Y - 1) (B w)‖ := congrArg norm heq
    _ ≤ ‖Y - 1‖ * ‖B w‖ := (Y - 1).le_opNorm _
    _ ≤ (1 / 4 : ℝ) * ‖B w‖ := mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
    _ = Real.sqrt 2 * ((1 / 4 : ℝ) * ‖w‖) := by rw [H]; ring

theorem exists_uniform_exponential_coframe_radius (n : ℕ) (hn : 0 < n)
    (r K : ℝ) (hr : 0 < r) (hK : 0 < K) :
    ∃ s : ℝ, 0 < s ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M) (p : M.Carrier)
      (U : ComplexVector n ≃L[ℂ] TangentVector M p),
      (∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
        (1 : Matrix (Fin n) (Fin n) ℂ) i j) →
      (∀ x ∈ distBall g.form p (2 * r), curvatureJetNorm g.form 0 x ≤ K) →
      ∀ v ∈ Metric.ball (0 : ComplexVector n) (4 * s),
        unitaryExponential g p U v ∈ distBall g.form p (2 * r) ∧
        ‖radialCoframe g p U v - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ) ∧
        (realMapDeriv (unitaryExponential g p U) v).IsInvertible := by
  obtain ⟨s, hs, hb⟩ := exists_uniform_physicalJacobi_radius n hn r K hr hK
  refine ⟨s, hs, ?_⟩
  intro M g p U hU hcurv v hv
  obtain ⟨himage, hJ⟩ := hb M g p U hU hcurv v hv
  have hA := radialCoframe_close_of_physicalJacobi g p U hU v hJ
  refine ⟨himage, hA, ?_⟩
  apply (radialCoframe_invertible_iff_realMapDeriv g p U v).mp
  exact Yau.LeafProofs.L21Aux.isInvertible_of_norm_sub_id_lt_one _
    (hA.trans_lt (by norm_num))

end Yau.Proofs.C04ChartsAux
