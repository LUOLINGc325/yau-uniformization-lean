import Yau.Proofs.C02NormalComplexStructure
import Yau.Proofs.C02NijenhuisPullback

/-! The actual normal-gauge complex structure is integrable throughout
the fixed open ball. The proof uses a valid original target chart locally. -/

noncomputable section
open Set Filter
open scoped Manifold InnerProductSpace ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalGaugeComplex_nijenhuis_zero (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hRm : ∀ y, inducedDistance g.form p y ≤ 1 → curvatureJetNorm g.form 0 y ≤ K)
    (x : ComplexVector n) (hx : ‖x‖ < radialGaugeRadius K) (v w : ComplexVector n) :
    LeafCandidates.nijenhuis (normalGaugeComplex g p U hU) x v w = 0 := by
  let c := normalRealMap g p U x
  let O := (normalRealMap g p U) ⁻¹' (chartAt (ComplexVector n) c).source
  have hO : IsOpen O :=
    (chartAt (ComplexVector n) c).open_source.preimage (normalRealMap_smooth g p U hU).continuous
  have hxO : x ∈ O := mem_chart_source _ _
  have hxBall : x ∈ Metric.ball (0 : ComplexVector n) (radialGaugeRadius K) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hF := (normalCoordinateMap_smooth g p U hU c).contDiffAt (hO.mem_nhds hxO)
  have hJ := ((normalGaugeComplex_smoothOn g p U hU hK hRm).mono
    Metric.ball_subset_closedBall).contDiffAt (Metric.isOpen_ball.mem_nhds hxBall)
  have hInjective : Function.Injective (fderiv ℝ (normalCoordinateMap g p U c) x) := by
    have hB := (isInvertible_of_close_identity (normalDifferential g p U hU x)
      ((normalGauge_low_order g p U hU hK hRm x hx.le).1.trans (by norm_num))).bijective.injective
    have hQ := (normalParallelCoefficients_isInvertible g p U hU c x hxO).bijective.injective
    intro a b hab
    apply hB
    apply hQ
    rw [normalDifferential_coords g p U hU c x a hxO,
      normalDifferential_coords g p U hU c x b hxO]
    exact hab
  apply nijenhuis_zero_of_local_intertwining (hF.of_le (by simp))
    (hJ.differentiableAt (by simp)) hInjective ?_ v w
  filter_upwards [hO.mem_nhds hxO, Metric.isOpen_ball.mem_nhds hxBall] with y hyO hyB
  apply ContinuousLinearMap.ext
  intro z
  exact normalGaugeComplex_intertwines g p U hU hK hRm c y z
    ((show ‖y‖ < radialGaugeRadius K by
      simpa only [Metric.mem_ball, dist_zero_right] using hyB).le) hyO

end Yau.Blueprint.C02Proof
