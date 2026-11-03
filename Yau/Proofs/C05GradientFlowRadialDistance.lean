import Yau.Proofs.C05GradientFlowFirstVariation

/-! The radial right upper distance derivative follows from the same genuine first variation. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1600000

theorem gradient_radial_distance_upperRightSlopeLE (g : SmoothMetric M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (o : M.Carrier) (a r : ℝ) (hr : 0 < r)
    (hHess : ∀ x ∈ distBall g.form o (2 * r), ∀ v : TangentVector M x,
      realHess g.form f x v v ≤ -a * realNormSq g.form x v)
    (β : ℝ → M.Carrier) (t : ℝ)
    (hD : 0 < inducedDistance g.form o (β t))
    (hx : β t ∈ distBall g.form o (2 * r)) :
    letI := manifold_realSmooth M
    IsMIntegralCurveAt β (realGradientVectorField g.form f) t →
    UpperRightSlopeLE (fun s => inducedDistance g.form o (β s)) t
      (realNorm g.form o (realGrad g.form f o) - a * inducedDistance g.form o (β t)) := by
  letI := manifold_realSmooth M
  intro hβ
  letI := underlyingRealTangentNormedAddCommGroup g.form o
  obtain ⟨v, hve, hvn, hprefix⟩ := exists_minimizing_radial_segment g o (β t)
  let p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨o, v⟩
  have hend : (realGeodesicFlow g p 1).proj = β t := hve
  have hmin : realTangentEnergy g.form p = inducedDistance g.form o (β t) ^ 2 := by
    rw [realTangentEnergy_eq_norm_sq]
    exact congrArg (fun q : ℝ => q ^ 2) hvn
  have hregion : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (realGeodesicFlow g p s).proj ∈ distBall g.form o (2 * r) := by
    intro s hs
    apply (mem_distBall_iff g o _ (by positivity)).mpr
    have H := hprefix s hs
    rw [realExponentialMap_smul] at H
    have hx' := (mem_distBall_iff g o _ (by positivity)).mp hx
    nlinarith only [H, hs.2, hD, hx']
  have hw := (gradient_integral_chart_eventually g f hf β t hβ).self_of_nhds.2
  have H := endpoint_distance_upperRightSlopeLE g p (fun _ => o) β t 0
    (realGradInChart g.form f (realGeodesicFlow g p 1).proj
      (chartPt (realGeodesicFlow g p 1).proj (realGeodesicFlow g p 1).proj))
    rfl hend.symm hD hmin contMDiffAt_const
    (gradient_integral_contMDiffAt_one g f hf β t hβ)
    (hasDerivAt_const _ _) (by simpa only [hend] using hw)
  rw [map_zero, neg_zero, zero_add,
    realChartMomentum_gradient g f hf (realGeodesicFlow g p 1).proj
      (realGeodesicFlow g p 1) (mem_chart_source _ _)] at H
  apply H.mono
  apply (div_le_iff₀ hD).mpr
  have HFTC := scalarVelocity_geodesic_terminal_le g f hf a
    (distBall g.form o (2 * r)) hHess p hregion
  rw [hmin, Real.sqrt_sq hD.le] at HFTC
  nlinarith only [HFTC]

end Yau.Proofs.C05GradientFlowAux
