import Yau.Proofs.P03NakanoLeviAlgebra

open scoped Manifold Matrix ComplexOrder

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- A genuine psh scalar weight adds a nonnegative Kronecker quadratic to
the computed Nakano curvature of any actual Hermitian coefficient bundle. -/
theorem weightedNakano_of_nakano_strictPsh (h : Metric (M := M) E)
    (hN : NakanoNonnegative (r := r) E h) (φ : M.Carrier → ℝ) (hφ : IsSmoothStrictPsh φ) :
    WeightedNakanoNonnegative (r := r) E h φ := by
  intro a z hz U
  unfold weightedCurvature
  rw [nakanoQuadratic_add]
  exact add_nonneg (hN a z hz U)
    (nakano_leviCorrection_nonnegative (strictPsh_chart_posDef hφ a hz.1).posSemidef
      (Yau.LeafProofs.L14Aux.metricMatrix_posDef E h a z hz).posSemidef U)

end Yau.NodeProofs.P03Aux
