import Yau.Proofs.V03DiscDifferential
import Yau.Proofs.V03Transitions

/-! The original base-disc differential, including its closed-disc within
representative, transported through actual manifold chart derivatives. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem baseDisc_fderivWithin_coords_change {f : ℂ → CotangentPoint M}
    (hf : CotangentDisc f) {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1)
    (x x' : M.Carrier) (hx : f ζ ∈ cotangentSource x) (hx' : f ζ ∈ cotangentSource x') :
    fderivWithin ℂ (fun η => chartPt x' (f η).1) (Metric.closedBall 0 1) ζ =
      (tangentCoordChange (ComplexModel n) x x' (f ζ).1).comp
        (fderivWithin ℂ (fun η => chartPt x (f η).1) (Metric.closedBall 0 1) ζ) := by
  let c : ℂ → ComplexVector n := fun η => chartPt x (f η).1
  let T : ComplexVector n → ComplexVector n := fun z => chartPt x' (chartInv x z)
  have hbase : chartInv x (c ζ) = (f ζ).1 := (extChartAt (ComplexModel n) x).left_inv hx
  have htarget : c ζ ∈ chartTarget x := (extChartAt (ComplexModel n) x).map_source hx
  have hT : DifferentiableAt ℂ T (c ζ) :=
    (chartTransition_contDiffAt x x' htarget (by rw [hbase]; exact hx')).differentiableAt (by simp)
  have hc : DifferentiableWithinAt ℂ c (Metric.closedBall 0 1) ζ :=
    (cotangentDisc_coords_contDiffWithinAt hf hζ x hx).fst.differentiableWithinAt (by simp)
  have hsource : ∀ᶠ η in 𝓝[Metric.closedBall 0 1] ζ, f η ∈ cotangentSource x :=
    (hf.1 ζ hζ).continuousWithinAt.preimage_mem_nhdsWithin
      ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hx)
  have heq : (fun η => chartPt x' (f η).1) =ᶠ[𝓝[Metric.closedBall 0 1] ζ] T ∘ c := by
    filter_upwards [hsource] with η hη
    exact congrArg (chartPt x') ((extChartAt (ComplexModel n) x).left_inv hη).symm
  rw [heq.fderivWithin_eq_of_mem hζ, fderiv_comp_fderivWithin ζ hT hc
    (uniqueDiffOn_complex_closedDisc ζ hζ)]
  have hDT := chartTransition_fderiv_eq_coordChange x x' htarget
  rw [hbase] at hDT
  rw [hDT]

def baseVelocityWithin (f : ℂ → CotangentPoint M) (ζ : ℂ) : TangentVector M (f ζ).1 :=
  chartVec (f ζ).1 (f ζ).1
    (fderivWithin ℂ (fun η => chartPt (f ζ).1 (f η).1) (Metric.closedBall 0 1) ζ 1)

theorem baseVelocityWithin_eq_fixed_chart {f : ℂ → CotangentPoint M}
    (hf : CotangentDisc f) {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1)
    (x : M.Carrier) (hx : f ζ ∈ cotangentSource x) :
    baseVelocityWithin f ζ = chartVec x (f ζ).1
      (fderivWithin ℂ (fun η => chartPt x (f η).1) (Metric.closedBall 0 1) ζ 1) := by
  have hself : f ζ ∈ cotangentSource (f ζ).1 := mem_extChartAt_source _
  have hD := congrArg (fun L : ℂ →L[ℂ] ComplexVector n => L 1)
    (baseDisc_fderivWithin_coords_change hf hζ (f ζ).1 x hself hx)
  simp only [ContinuousLinearMap.comp_apply] at hD
  rw [hD]
  exact (chartVec_transition x (f ζ).1 (f ζ).1 hx hself _).symm

set_option backward.isDefEq.respectTransparency false in
theorem baseDisc_coordinate_derivative {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    {ζ : ℂ} (hζ : ζ ∈ Metric.ball 0 1) (x : M.Carrier) (hx : f ζ ∈ cotangentSource x) :
    tangentCoords x (f ζ).1
      (mfderiv 𝓘(ℂ, ℂ) (ComplexModel n) (fun η => (f η).1) ζ
        ((tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm 1)) =
      fderiv ℂ (fun η => chartPt x (f η).1) ζ 1 := by
  have hnhds : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 ζ :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hζ) Metric.ball_subset_closedBall
  have hfd := ((hf.1.contMDiffAt hnhds).mdifferentiableAt (by simp))
  have hxbase : (f ζ).1 ∈ (extChartAt (ComplexModel n) x).source := hx
  have hca : MDifferentiableAt (ComplexModel n) 𝓘(ℂ, ComplexVector n) (chartPt x) (f ζ).1 :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hxbase)
  have hc := mfderiv_comp_apply ζ hca hfd
    ((tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm 1)
  rw [mfderiv_eq_fderiv] at hc
  exact hc.symm

theorem baseVelocityWithin_eq_mfderiv {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    {ζ : ℂ} (hζ : ζ ∈ Metric.ball 0 1) :
    baseVelocityWithin f ζ =
      mfderiv 𝓘(ℂ, ℂ) (ComplexModel n) (fun η => (f η).1) ζ
        ((tangentSpaceCastModel 𝓘(ℂ, ℂ) ζ).symm 1) := by
  have hself : f ζ ∈ cotangentSource (f ζ).1 := mem_extChartAt_source _
  have hnhds : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 ζ :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hζ) Metric.ball_subset_closedBall
  unfold baseVelocityWithin
  rw [fderivWithin_of_mem_nhds hnhds, ← baseDisc_coordinate_derivative hf hζ (f ζ).1 hself,
    chartVec_tangentCoords _ _ hself]

end Yau.Blueprint.V03Proof
