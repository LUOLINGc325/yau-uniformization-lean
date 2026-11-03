import Yau.Proofs.C02ParallelComplexField
import Yau.Proofs.C02RadialFrameFlow
import Yau.LeafProofs.L12JacobiCurvature

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalParallelCoefficients_origin (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (z : ComplexVector n) :
    normalParallelCoefficients g p U hU p 0 z =
      tangentCoords p p (U ((Real.sqrt (2 : ℝ))⁻¹ • z)) := by
  have ht := normalParallelTotalSpace_radial g p U hU 0 z 0
  rw [zero_smul, realParallelTransportFlow_zero] at ht
  have hc := congrArg (fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier => (realPhaseChart p q).2) ht
  change normalParallelCoefficients g p U hU p 0 z = realTangentCoords p p (normalInitialLinearMap p U z) at hc
  rw [realTangentCoords_eq_complex_self, normalInitialLinearMap_coordinates] at hc
  exact hc

theorem normalParallelCoefficients_origin_I (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (z : ComplexVector n) :
    normalParallelCoefficients g p U hU p 0 (Complex.I • z) =
      Complex.I • normalParallelCoefficients g p U hU p 0 z := by
  rw [normalParallelCoefficients_origin, normalParallelCoefficients_origin]
  change (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) p) p)
      (U ((Real.sqrt (2 : ℝ))⁻¹ • (Complex.I • z))) = _
  rw [smul_comm (Real.sqrt (2 : ℝ))⁻¹ Complex.I z, map_smul, map_smul]
  rfl

theorem normalParallelComplex_zero (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    normalParallelComplex g p U hU 0 = complexStructureCLM n := by
  have hx : normalRealMap g p U 0 ∈ (chartAt (ComplexVector n) p).source := by
    rw [normalRealMap_zero]
    exact mem_chart_source _ _
  rw [normalParallelComplex_eq_chart g p U hU p 0 hx]
  apply ContinuousLinearMap.ext
  intro z
  apply (normalParallelCoefficients_isInvertible g p U hU p 0 hx).bijective.injective
  change normalParallelCoefficients g p U hU p 0 (normalParallelComplexInChart g p U hU p 0 z) =
    normalParallelCoefficients g p U hU p 0 (Complex.I • z)
  exact (normalParallelComplex_reconstruct g p U hU p 0 z hx).trans
    (normalParallelCoefficients_origin_I g p U hU z).symm

end Yau.Blueprint.C02Proof
