import Yau.Proofs.C02ChernCoefficientCone
import Yau.Proofs.C02CurvatureBasisTrace
import Yau.Proofs.C02UnitaryFrameMatrix
import Yau.Proofs.C02CurvatureCompact
import Yau.Proofs.P06ScalarUniquenessRicciContraction

/-! The finite positive coefficient trace is exactly the original scalar
curvature of the supplied field, by the actual Ricci--Chern identity. -/

noncomputable section
open scoped Matrix ComplexOrder InnerProductSpace Manifold Matrix.Norms.Elementwise
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

def unitaryChernArray (h : HermitianField M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p) : CurvatureArray n :=
  curvatureHermitianPart (curvatureBasisTransform (actualChernArray h p) (unitaryFrameMatrix p U))

theorem unitaryChernArray_trace (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (h p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    curvatureTrace (unitaryChernArray h p U) = scalarCurvature h p := by
  rw [unitaryChernArray, curvatureTrace_hermitianPart]
  change curvatureTrace (curvatureBasisTransform (actualChernArray h p) (unitaryFrameMatrix p U)) =
    traceWith (gMat h p) (ricci h p)
  apply curvatureTrace_basisTransform_eq_traceWith _ _ _ _ (unitaryFrameMatrix_gram h p U hU)
  intro a b
  rw [Yau.NodeProofs.P06Aux.ricci_eq_chern_contraction h hs hk p a b, Finset.sum_comm]
  rfl

theorem exists_uniform_unitaryChern_coefficient_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (M : ComplexManifold n) (h : HermitianField M),
      MetricSmooth h → KahlerClosed h → NonnegBisectional h → ∀ p : M.Carrier,
      ∀ U : ComplexVector n ≃ₗ[ℂ] TangentVector M p,
      (∀ u v, (h p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) →
      ‖unitaryChernArray h p U‖ ≤ D * scalarCurvature h p := by
  obtain ⟨D, hD, hbound⟩ := exists_curvature_coefficient_trace_bound n
  refine ⟨D, hD, ?_⟩
  intro M h hs hk hBisec p U hU
  have hPos : CurvaturePositive (unitaryChernArray h p U) :=
    actualChernArray_basis_positive h hBisec p (unitaryFrameMatrix p U)
  simpa only [unitaryChernArray_trace h hs hk p U hU] using hbound _ hPos

end Yau.Blueprint.C02Proof
