import Yau.Proofs.P03HolomorphicFunctionSpace
import Yau.Proofs.P03MovingCompactPairings
import Yau.LeafProofs.L17HolomorphicCauchy

open scoped Manifold Topology
open Set Filter MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs.L17Holomorphic

variable {n : ℕ} {M : ComplexManifold n}

/-- The actual complex directional derivative depends jointly continuously
on the holomorphic function and the point in a fixed buffered coordinate ball.
The derivative is expressed by the already proved single-circle formula. -/
theorem continuous_directionalEvaluation_on_ball (a : M.Carrier) (z₀ v : ComplexVector n)
    {ρ : ℝ} (hρ : 0 < ρ) (hsub : Metric.closedBall z₀ ρ ⊆ chartTarget a) :
    Continuous (fun p : holomorphicFunctions M × Metric.ball z₀ (ρ / 4) =>
      fderiv ℂ (inChart a (p.1.1 : M.Carrier → ℂ)) p.2.1 v) := by
  letI := manifold_locallyCompact M
  let R := (ρ / 4) / (1 + ‖v‖)
  have hR : 0 < R := by dsimp [R]; positivity
  let Θ := Icc (0 : ℝ) (2 * Real.pi)
  let μ : Measure Θ := volume.comap (Subtype.val : Θ → ℝ)
  letI : IsFiniteMeasureOnCompacts μ :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe measurableSet_Icc)
  have htube : ∀ p : Metric.ball z₀ (ρ / 4) × Θ,
      p.1.1 + circleMap 0 R p.2.1 • v ∈ chartTarget a := by
    intro p
    exact lineTube_mem hρ hsub (Metric.ball_subset_closedBall p.1.2)
      (circleMap_mem_closedBall hR _)
  have htubeCont : Continuous (fun p : Metric.ball z₀ (ρ / 4) × Θ =>
      p.1.1 + circleMap 0 R p.2.1 • v) := by fun_prop
  let j : Metric.ball z₀ (ρ / 4) × Θ → M.Carrier := fun p =>
    chartInv a (p.1.1 + circleMap 0 R p.2.1 • v)
  have hj : Continuous j :=
    (continuousOn_extChartAt_symm (I := ComplexModel n) a).comp_continuous htubeCont htube
  let w : C(Θ, ℂ) := ⟨fun θ => lineWeight R θ.1,
    (lineWeight_continuous hR).comp continuous_subtype_val⟩
  have hc := (continuous_moving_compactPairing μ j hj w).comp
    (continuous_subtype_val.prodMap continuous_id :
      Continuous (fun p : holomorphicFunctions M × Metric.ball z₀ (ρ / 4) => (p.1.1, p.2)))
  apply hc.congr
  intro p
  change (∫ θ : Θ, lineWeight R θ.1 * inChart a (p.1.1 : M.Carrier → ℂ)
    (p.2.1 + circleMap 0 R θ.1 • v) ∂volume.comap (Subtype.val : Θ → ℝ)) = _
  rw [integral_subtype_comap (s := Θ) measurableSet_Icc
    (fun θ => lineWeight R θ * inChart a (p.1.1 : M.Carrier → ℂ)
      (p.2.1 + circleMap 0 R θ • v))]
  exact directional_eq_lineIntegral (isOpen_extChartAt_target a)
    ((mdifferentiable_iff_chartDifferentiable (p.1.1 : M.Carrier → ℂ)).mp p.1.2 a) hR
    (fun ζ hζ => lineTube_mem hρ hsub (Metric.ball_subset_closedBall p.2.2) hζ)

end Yau.NodeProofs.P03Aux
