import Yau.Proofs.P03ChartDifferentials

/-! V01 scratch source: reuse the actual canonical P03 chart-frame bridge
for the differential of the given base immersion. -/

noncomputable section
open scoped Manifold Topology

namespace Yau.Blueprint.V01Proof

variable {n N : ℕ} {M : ComplexManifold n}

theorem base_chart_derivative_injective
    (F : M.Carrier → ComplexVector N) (hF : IsHolomorphicVecMap F)
    (hImm : IsImmersionMap F) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    Function.Injective (fderiv ℂ (inChart a F) (chartPt a x)) := by
  rw [Yau.NodeProofs.P03Aux.chartDerivative_eq_intrinsic_comp F hF a x hx]
  exact (hImm x).comp (Yau.NodeProofs.P03Aux.chartFrameEquiv a x hx).injective

end Yau.Blueprint.V01Proof
