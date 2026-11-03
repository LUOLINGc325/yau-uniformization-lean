import Yau.Proofs.V03HolomorphicDirichletDerivative
import Yau.Proofs.V03ScalarAreaFourier
import Yau.Proofs.V03HolomorphicQuadratic
import Yau.Proofs.V03MixedRealLinear

/-! The actual scalar holomorphic area has its exact mixed parameter
derivative, with all holomorphic acceleration terms canceled natively. -/

open scoped Topology ContDiff lp
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem holomorphicScalarArea_eq_norm_sq {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ U) :
    (normDiscArea (fun ζ => H (z, ζ))).toReal =
      (2 * Real.pi) * ‖holomorphicFamilyDirichletVector hU hH z‖ ^ 2 := by
  have hs : ContDiffOn ℂ ∞ (fun ζ => H (z, ζ)) (Metric.closedBall (0 : ℂ) 1) :=
    hH.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun ζ hζ => ⟨hz, hζ⟩)
  rw [normDiscArea_scalar_eq_boundaryDSq hs, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    holomorphicFamilyDirichletVector_norm_sq hU hH hz]

theorem holomorphicScalarArea_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (fun z => (normDiscArea (fun ζ => H (z, ζ))).toReal) U := by
  have hh : ContDiffOn ℝ ∞ (fun z => (2 * Real.pi) *
      ‖holomorphicFamilyDirichletVector hU hH z‖ ^ 2) U :=
    contDiffOn_const.mul (((holomorphicFamilyDirichletVector_contDiffOn hU hH).restrict_scalars ℝ).norm_sq ℂ)
  exact hh.congr (fun z hz => holomorphicScalarArea_eq_norm_sq hU hH hz)

theorem holomorphicScalarArea_mixed {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1)) :
    mixedReal (fun z => (normDiscArea (fun ζ => H (z, ζ))).toReal) =
      (2 * Real.pi) * (boundaryDSq
        (fun θ (_ : Unit) => jointParameterVelocity H U 0 1 (circlePoint θ))).toReal := by
  let Q := holomorphicFamilyDirichletVector hU hH
  have hQ : ContDiffAt ℂ 2 Q 0 :=
    ((holomorphicFamilyDirichletVector_contDiffOn hU hH).contDiffAt (hU.mem_nhds h0)).of_le (by simp)
  have heq : (fun z => (normDiscArea (fun ζ => H (z, ζ))).toReal) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => (2 * Real.pi) * ‖Q z‖ ^ 2) := by
    filter_upwards [hU.mem_nhds h0] with z hz
    exact holomorphicScalarArea_eq_norm_sq hU hH hz
  rw [mixedReal_congr heq, mixedReal_const_mul ((hQ.restrict_scalars ℝ).norm_sq ℂ),
    mixedReal_holomorphic_norm_sq hQ, fderiv_holomorphicFamilyDirichletVector_norm_sq hU hH h0]

end Yau.Blueprint.V03Proof
