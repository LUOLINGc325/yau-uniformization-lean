import Yau.Proofs.C04BoundedGeometryChartsRadialFrame

/-! Exact real pullback identities in the actual radial coframe. -/

noncomputable section
open scoped Topology Manifold ContDiff Matrix InnerProductSpace

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem radialParallelFrame_radialCoframe (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v w : ComplexVector n) :
    radialParallelFrame g p U v (radialCoframe g p U v w) =
      realMapDeriv (unitaryExponential g p U) v w := by
  exact (radialParallelFrame g p U v).apply_symm_apply _

theorem realPullbackMetric_eq_radial_gram (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) (v : ComplexVector n) (a b : RIdx n) :
    realPullbackMetric g.form (unitaryExponential g p U) v a b =
      2 * (⟪radialCoframe g p U v (realVec a),
        radialCoframe g p U v (realVec b)⟫_ℂ).re := by
  change (underlyingRealRiemannianMetric g.form).inner (unitaryExponential g p U v)
      (realMapDeriv (unitaryExponential g p U) v (realVec a))
      (realMapDeriv (unitaryExponential g p U) v (realVec b)) = _
  rw [← radialParallelFrame_radialCoframe g p U v (realVec a),
    ← radialParallelFrame_radialCoframe g p U v (realVec b)]
  exact radialParallelFrame_metric g p U hU v _ _

end Yau.Proofs.C04ChartsAux
