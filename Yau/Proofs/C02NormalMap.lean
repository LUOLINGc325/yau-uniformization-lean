import Yau.Proofs.C02UnitaryRealFrame
import Yau.Proofs.C02GeodesicSmooth

/-! The normal parametrizations are actual exponential maps at physical time
one. The sqrt(2) is solely a source-coordinate dilation. No injectivity of the
map is asserted; later Jacobi estimates address its actual differential. -/

noncomputable section
open scoped Manifold ContDiff InnerProductSpace
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def normalRealMap (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p) (v : ComplexVector n) : M.Carrier :=
  realExponentialMap g p (normalInitialLinearMap p U v)

def normalUnitaryMap (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p) (v : ComplexVector n) : M.Carrier :=
  normalRealMap g p U (Real.sqrt (2 : ℝ) • v)

theorem normalRealMap_zero (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p) : normalRealMap g p U 0 = p := by
  rw [normalRealMap, map_zero, realExponentialMap_zero]

theorem normalUnitaryMap_eq_exponential (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p) (v : ComplexVector n) :
    normalUnitaryMap g p U v = realExponentialMap g p ((realTangentEquiv p).symm (U v)) := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  change realExponentialMap g p ((realTangentEquiv p).symm
    (U ((Real.sqrt (2 : ℝ))⁻¹ • (Real.sqrt (2 : ℝ) • v)))) = _
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul]

theorem normalRealMap_radial (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p) (v : ComplexVector n) (s : ℝ) :
    normalRealMap g p U (s • v) =
      (realGeodesicFlow g (⟨p, normalInitialLinearMap p U v⟩ :
        TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s).proj := by
  rw [normalRealMap, map_smul, realExponentialMap_smul]

theorem normalRealMap_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    letI := manifold_realSmooth M
    ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞ (normalRealMap g p U) := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form p
  letI := underlyingRealTangentInnerProductSpace g.form p
  have hW : ContMDiff 𝓘(ℝ, ComplexVector n)
      𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p) ∞ (normalInitialLinearMap p U) :=
    (normalInitialIsometry g.form p U hU).toContinuousLinearMap.contMDiff
  exact (realExponentialMap_smooth g p).comp hW

theorem normalRealMap_distance_le (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (v : ComplexVector n) :
    inducedDistance g.form p (normalRealMap g p U v) ≤ ‖v‖ := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form p
  letI := underlyingRealTangentInnerProductSpace g.form p
  exact (inducedDistance_realExponentialMap_le g p (normalInitialLinearMap p U v)).trans_eq
    (normalInitialLinearMap_norm g.form p U hU v)

theorem normalUnitaryMap_distance_le (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (v : ComplexVector n) :
    inducedDistance g.form p (normalUnitaryMap g p U v) ≤ Real.sqrt (2 : ℝ) * ‖v‖ := by
  have h := normalRealMap_distance_le g p U hU (Real.sqrt (2 : ℝ) • v)
  simpa only [normalUnitaryMap, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] using h

end Yau.Blueprint.C02Proof
