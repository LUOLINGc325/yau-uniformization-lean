import Yau.Proofs.C02UnitaryCurvatureCoefficients
import Yau.Proofs.C02UnitaryFrame

/-! A dimension constant controls the original physical curvature norm
by the original scalar curvature under nonnegative bisectional curvature. -/

noncomputable section
open scoped Matrix Matrix.Norms.Elementwise Manifold InnerProductSpace
namespace Yau.Blueprint.C02Proof

theorem exists_curvatureJetNorm_zero_scalar_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M),
      NonnegBisectional g.form → ∀ p : M.Carrier,
      curvatureJetNorm g.form 0 p ≤ C * scalarCurvature g.form p := by
  obtain ⟨A, hA, hReal⟩ := exists_realCurvatureCoefficient_norm_bound n
  obtain ⟨D, hD, hCoefficient⟩ := exists_uniform_unitaryChern_coefficient_bound n
  refine ⟨A * D, mul_pos hA hD, ?_⟩
  intro M g hBisec p
  obtain ⟨U, hU⟩ := exists_unitaryTangentFrame g.form p
  rw [curvatureJetNorm_zero_eq_unitaryChern_norm g p U hU]
  calc
    _ ≤ A * ‖unitaryChernArray g.form p U‖ := hReal _
    _ ≤ A * (D * scalarCurvature g.form p) := mul_le_mul_of_nonneg_left
      (hCoefficient M g.form (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g)
        g.kahler_equations hBisec p U hU) hA.le
    _ = _ := by ring

end Yau.Blueprint.C02Proof
