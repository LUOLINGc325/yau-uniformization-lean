import Yau.Proofs.C04BoundedGeometryChartsRadialComplex
import Yau.Proofs.C04BoundedGeometryChartsRadialPullback

/-! Exact conjugation formula for the actual pulled complex structure. -/

noncomputable section
open scoped Topology Manifold ContDiff Matrix

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem realMapDeriv_eq_radial_frame_comp (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    realMapDeriv (unitaryExponential g p U) v =
      (radialParallelFrame g p U v).toContinuousLinearMap.comp (radialCoframe g p U v) := by
  ext w
  exact (radialParallelFrame_radialCoframe g p U v w).symm

theorem realPullbackJ_eq_radial_conjugation (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (v w : ComplexVector n) :
    realPullbackJ (unitaryExponential g p U) v w =
      (radialCoframe g p U v).inverse (Complex.I • radialCoframe g p U v w) := by
  rw [realPullbackJ, realMapDeriv_eq_radial_frame_comp]
  rw [ContinuousLinearMap.inverse_equiv_comp]
  simp only [ContinuousLinearMap.comp_apply]
  apply congrArg (radialCoframe g p U v).inverse
  have H := congrArg (radialParallelFrame g p U v).symm
    (radialParallelFrame_intertwines g hk p U v (radialCoframe g p U v w))
  simpa only [ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] using H.symm

theorem radialCoframe_invertible_iff_realMapDeriv (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    (radialCoframe g p U v).IsInvertible ↔
      (realMapDeriv (unitaryExponential g p U) v).IsInvertible := by
  rw [realMapDeriv_eq_radial_frame_comp]
  simp

end Yau.Proofs.C04ChartsAux
